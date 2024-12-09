#include "assert.h"
#include "config/testpath.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "frontend/btor2_encoder.h"
#include "smt-switch/bitwuzla_factory.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/identity_walker.h"
#include "smt-switch/smtlib_reader.h"
#include "smt-switch/substitution_walker.h"
#include "smt-switch/utils.h"

#include <iomanip>
#include <chrono>
#include <gmp.h>
#include <gmpxx.h>
#include <iostream>
#include <algorithm>
#include <random>

#include "btor_sweeping.h"
#include "smt-switch/utils.h"

using namespace smt;
using namespace std;
using namespace wasim;

class NodeData {
private:
    Term term;
    size_t bit_width;
    std::vector<BtorBitVector> simulation_data;
public:
    NodeData() : term(nullptr), bit_width(0) {} 

    NodeData(const Term & t) : term(t), bit_width(0) {}

    NodeData(const Term & t, const size_t & bw) : term(t), bit_width(bw) {}

    Term get_term() const { return term; }
    
    size_t get_bit_width() const { return bit_width; }
    
    const std::vector<BtorBitVector>& get_simulation_data() const {
        return simulation_data; 
    }

    void add_data(const BtorBitVector & data) {
        simulation_data.push_back(data);
    }
};

void create_lut(Term term, std::unordered_map<std::string, std::string>& lut) {
    // term: (store (store (store ... (store array index elemnent) ...)))
    // create a lookup table for each index

    // Traverse nested stored op
    Term current = term;
    while (current->get_op().prim_op == PrimOp::Store) {
        auto children = TermVec(current->begin(), current->end());
        if (children.size() != 3) {
            throw std::runtime_error("Store operation should have exactly 3 children");
        }
        // store：array、index、value
        auto array = children[0];   // original array
        auto index = children[1];   // stored position
        auto value = children[2];   // sotred value

        // insert index and value
        // std::cout<< "stored position:" <<std::endl;
        // std::cout<< "stored position" << index->to_string().data() << std::endl;
        // std::cout<< "stored value" << value->to_string().data() << std::endl;
        // if(!index->to_string().empty() && !value->to_string().empty()
        //     && index->to_string().find("#b") == 0 && value->to_string().find("#b") == 0) {
        //         std::string index_str = index->to_string().substr(2);
        //         std::string value_str = value->to_string().substr(2);
        //     }

        lut[index->to_string().substr(2)] = value->to_string().substr(2);
        current = array; // next iteration
    }
    // print lut
    // std::cout << "lut size: " << lut.size() << std::endl;
    // for (const auto & [idx, val] : lut) {
    //     std::cout << "index: " << idx << ", value: " << val << std::endl;
    // }
}

// RAII wrapper for GMP random state
class GmpRandStateGuard
{
    gmp_randstate_t state;

    public:
    GmpRandStateGuard()
    {
        gmp_randinit_default(state);
        gmp_randseed_ui(state, time(NULL));
    }

    ~GmpRandStateGuard() { gmp_randclear(state); }

    void random_128(mpz_t & rand_num)
    {
        mpz_init2(rand_num, 128);
        mpz_urandomb(rand_num, state, 128);
    }

    // operator gmp_randstate_t &() { return state; }
};

std::chrono::time_point<std::chrono::high_resolution_clock> last_time_point;
void print_time() {
    auto now = std::chrono::high_resolution_clock::now();
    auto elapsed_time = std::chrono::duration_cast<std::chrono::milliseconds>(now - last_time_point).count();
    last_time_point = now;  // Update last time point
    std::cout << "[" << elapsed_time << " ms]  ";
}

int main() {
    last_time_point = std::chrono::high_resolution_clock::now();

    cout << "Starting program...\n";
    auto start_time = std::chrono::high_resolution_clock::now();

    SmtSolver solver = BoolectorSolverFactory::create(false);

    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    cout << "Loading and parsing BTOR2 files...\n";
    TransitionSystem sts1(solver);
    BTOR2Encoder btor_parser1("../design/idpv-test/aes_case/AES_TOP.btor2", sts1, "a::");

    auto a_key_term = sts1.lookup("a::key");
    auto a_input_term = sts1.lookup("a::datain");
    auto a_output_term = sts1.lookup("a::finalout");

    TransitionSystem sts2(solver);
    BTOR2Encoder btor_parser2("../design/idpv-test/aes_case/AES_Verilog.btor2", sts2, "b::");

    auto b_key_term = sts2.lookup("b::key");
    auto b_input_term = sts2.lookup("b::in");
    auto b_output_term = sts2.lookup("b::out");

    // Assert constraints
    // init assertion - base context
    print_time();
    cout << "init solver" << endl;

    solver->assert_formula(sts1.init());
    solver->assert_formula(sts2.init());
    for (const auto & c : sts1.constraints()) solver->assert_formula(c.first);
    for (const auto & c : sts2.constraints()) solver->assert_formula(c.first);

    solver->push(); // context level 1

    if (!a_key_term || !a_input_term || !b_input_term || !b_key_term || !a_output_term || !b_output_term) {
        throw std::runtime_error("Required terms not found in models");
    }

    auto root = solver->make_term(Equal, a_output_term, b_output_term);

    std::unordered_map<Term, NodeData> node_data_map; // term -> sim_data
    std::unordered_map<size_t, TermVec> hash_term_map; // hash -> TermVec
    std::unordered_map<Term, Term> substitution_map; // term -> term, for substitution
    std::unordered_map<Term, std::unordered_map<std::string, std::string>> all_luts; // state -> lookup table
    std::unordered_map<std::string, std::string> lut_a;//index-> val in a
    std::unordered_map<std::string, std::string> lut_b;//index-> val in b

    // ARRAY INIT
    for (const auto & var_val_pair : sts1.init_constants()) {
        if(var_val_pair.first->get_sort()->get_sort_kind() != ARRAY)
            continue;
        Term val = var_val_pair.second;
        create_lut(val, lut_a);
        all_luts[var_val_pair.first] = lut_a;
    }

    for (const auto & var_val_pair : sts2.init_constants()) {
        if(var_val_pair.first->get_sort()->get_sort_kind() != ARRAY)
            continue;
        Term val = var_val_pair.second;
        
        create_lut(val, lut_b);
        all_luts[var_val_pair.first] = lut_b;
    }

    // for (const auto & lut_pair : all_luts) {
    //     cout << "LUT " << lut_pair.first << " size: " << lut_pair.second.size() << endl;
    // }
    //End of array init

    //simulation
    GmpRandStateGuard rand_guard;
    int num_iterations = 10;

    for (int i = 0; i < num_iterations; ++i) {
        mpz_t key_mpz, input_mpz;
        rand_guard.random_128(key_mpz);
        rand_guard.random_128(input_mpz);

        // Use RAII for GMP strings
        unique_ptr<char, void (*)(void *)> key_str(mpz_get_str(NULL, 10, key_mpz), free);
        unique_ptr<char, void (*)(void *)> input_str(mpz_get_str(NULL, 10, input_mpz), free);

        mpz_clear(key_mpz);
        mpz_clear(input_mpz);

        auto bv_key = btor_bv_char_to_bv(key_str.get());
        auto bv_input = btor_bv_char_to_bv(input_str.get());

        //store sim data in NodeData
        node_data_map[a_key_term].add_data(*bv_key);
        node_data_map[a_input_term].add_data(*bv_input);
        node_data_map[b_key_term].add_data(*bv_key);
        node_data_map[b_input_term].add_data(*bv_input);
       
    }  // end of simulation

    assert(node_data_map[a_key_term].get_simulation_data().size() == num_iterations);
    assert(node_data_map[a_input_term].get_simulation_data().size() == num_iterations);
    assert(node_data_map[b_key_term].get_simulation_data().size() == num_iterations);
    assert(node_data_map[b_input_term].get_simulation_data().size() == num_iterations);

    //start post order traversal
    std::stack<std::pair<Term,bool>> node_stack;
    node_stack.push({root,false});

    while(!node_stack.empty()) {
        auto & [current,visited] = node_stack.top();
        if(node_data_map.find(current) != node_data_map.end()) {
            node_stack.pop();
            continue;
        }

        if(!visited) {
            // push all children onto stack
            for(Term child : current) {
                if(current->get_sort()->get_sort_kind() == BV || current->get_sort()->get_sort_kind() == BOOL) {
                    node_stack.push({child,false});
                }  
            }
            visited = true;
        } else {
            if(current->is_value()) { //constant & constant array
                // cout << "This is a constant node, ";
                auto current_str = current->to_string();
                if(!current_str.empty() && current_str.find("#b") == 0) {
                    current_str = current_str.substr(2);
                }
                cout << "current_str: " << current_str << endl;

                //term current , string current_str
                NodeData& nd = node_data_map[current];
                auto current_bv = btor_bv_char_to_bv(current_str.data());
                auto node_bv_hash = btor_bv_hash(current_bv);

                if(hash_term_map.find(node_bv_hash) == hash_term_map.end()){ // new hash
                    hash_term_map.insert({node_bv_hash, {current}});
                    substitution_map.insert({current, current}); // no substitution
                    for (int i = 0; i < num_iterations; ++i) {
                        nd.add_data(*current_bv);
                    }
                } else {
                    if(substitution_map.find(current) != substitution_map.end()){ // if already substituted
                        auto val = node_data_map[substitution_map[current]].get_simulation_data();
                        NodeData& nd = node_data_map[current];
                        for(int i = 0; i < num_iterations; i++) {
                            nd.add_data(val[i]);
                        }
                        current = substitution_map[current];
                    }
                    else {
                        auto &terms = hash_term_map[node_bv_hash];// exist potential substitution
                        terms.push_back(current); // add current to terms
                        for(const auto & t : terms) {
                            TermVec not_equal_pair = {solver->make_term(Not, solver->make_term(Equal, t, current))};
                            auto res = solver->check_sat_assuming(not_equal_pair);
                            if(res.is_unsat()) {
                                substitution_map.insert({t, current});
                                current_bv = btor_bv_char_to_bv(t->to_string().data());
                                break;
                            }else {
                                substitution_map.insert({current, current}); // no substitution
                            }
                        }
                    }    
                }
                assert (nd.get_simulation_data().size() == num_iterations);
                btor_bv_free(current_bv);
            }
            else if(current->is_symbolic_const() && current->get_op().is_null()) { // variants only for input and key FIXME: why arrays arrive here?
                // cout << "This is symbolic const node" << endl;
                // cout << "current: " << current->to_string() << endl;
                assert(node_data_map.find(current) != node_data_map.end());

                substitution_map.insert({current, current}); // no substitution
                if(all_luts.find(current) != all_luts.end()) {
                    cout << "This array node is in LUT" << endl;
                    auto & lut = all_luts[current];
                    NodeData& nd = node_data_map[current];
                    int count = 0;
                    for(auto & [idx, val] : lut) { //FIXME: random select
                        if (count >= num_iterations)
                            break;
                        cout << "index: " << idx << ", value: " << val << endl;
                        auto val_bv = btor_bv_char_to_bv(val.data());
                        nd.add_data(*val_bv);
                        btor_bv_free(val_bv);
                        count += 1;
                    }
                    // cout << node_data_map[current].get_simulation_data().size() << endl;
                }                
                assert(node_data_map[current].get_simulation_data().size() == num_iterations);
            }
            else { // compute simulation data for current node
                auto op_type = current->get_op();
                NodeData& nd = node_data_map[current];
                // cout << "operation type: " << op_type.to_string() << endl;

                // first, find and check substitution
                if(//TODO:) {
                    for(size_t i = 0; i < num_iterations; i++) {
                        nd.add_data(node_data_map[substitution_map[current]].get_simulation_data()[i]);
                    }
                    current = substitution_map[current];
                    node_stack.pop();
                    continue;
                }





                TermVec children(current->begin(), current->end());
                auto child_size = children.size();
                cout << "children size: " << child_size << endl;

                if(child_size == 2 && visited) {
                    std::cout << "This is a 2-child node." << std::endl;
                    

                    for(size_t i = 0; i < num_iterations; i++) {
                        auto & sim_data_1 = node_data_map[children[0]].get_simulation_data();
                        auto & sim_data_2 = node_data_map[children[1]].get_simulation_data();

                        assert(sim_data_1.size() == num_iterations && sim_data_2.size() == num_iterations);

                        auto btor_child_1 = sim_data_1[i];
                        auto btor_child_2 = sim_data_2[i]; 

                        //FIXME: whether to extend bit width or not
                        auto btor_child_1_fix_width = btor_bv_uext(&btor_child_1, 128 - btor_child_1.width);
                        auto btor_child_2_fix_width = btor_bv_uext(&btor_child_2, 128 - btor_child_2.width);

                        // cout << "child 1: " << btor_child_1_fix_width->width << " " <<btor_child_1_fix_width->len << " " <<btor_child_1_fix_width->bits << endl;
                        // cout << "child 2: " << btor_child_2_fix_width->width << " " <<btor_child_2_fix_width->len << " " <<btor_child_2_fix_width->bits << endl;

                        if(op_type.prim_op == PrimOp::BVAdd) {
                            cout << "BVAdd" << endl;
                            auto current_val = btor_bv_add(btor_child_1_fix_width, btor_child_2_fix_width);
                            nd.add_data(*current_val);
                        }
                        
                        else if(op_type.prim_op == PrimOp::BVAnd) {
                            cout << "BVAnd" << endl;
                            auto current_val = btor_bv_and(btor_child_1_fix_width, btor_child_2_fix_width);
                            nd.add_data(*current_val);
                        }
                        else if(op_type.prim_op == PrimOp::Select) {
                            cout << "Select" << endl;
                            //FIXME: error here
                            auto children = TermVec(current->begin(), current->end());
                            assert(children.size() == 2);
                            auto data = node_data_map[children[0]].get_simulation_data();
                            assert(data.size() == num_iterations);
                            nd.add_data(data[i]);   
                        }

                        else if(op_type.prim_op == PrimOp::Concat) {
                            cout << "Concat" << endl;
                            cout << "current: " << current->to_string() << endl;
                            auto current_val = btor_bv_concat(btor_child_1_fix_width, btor_child_2_fix_width);
                            nd.add_data(*current_val);

                        }

                        else {
                            throw NotImplementedException("Unsupported operator type3: " + op_type.to_string());
                        }
                    }
                    node_data_map.insert({current, nd});
                }
                else if(child_size == 1) {
                    std::cout << "This is a 1-child node." << std::endl;
                    cout << "current: " << current->to_string() << endl;
                    NodeData& nd = node_data_map[current];
                    
                    for(size_t i = 0; i < num_iterations; i++) {
                        auto & sim_data = node_data_map[children[0]].get_simulation_data();
                        cout << sim_data.size() << endl; 
                        assert(sim_data.size() == num_iterations);

                        auto btor_child = sim_data[i];

                        if(op_type.prim_op = PrimOp::BVNot) {
                            cout << "BVNot" << endl;
                            auto current_val = btor_bv_not(&btor_child);
                            nd.add_data(*current_val);
                            
                        }
                        else if(op_type.prim_op == PrimOp::Extract) {
                            cout << "Extract" << endl;
                            auto high = op_type.idx0;
                            auto low = op_type.idx1;
                            auto current_val = btor_bv_slice(&btor_child, high, low);
                            nd.add_data(*current_val);
                           
                        }
                        else if(op_type == PrimOp::Concat) {
                            cout << "Concat" << endl;
                        }
                        else if(op_type == PrimOp::BVNeg) {
                            cout << "BVNeg" << endl;
                        }
                        else {
                            throw NotImplementedException("Unsupported operator type1: " + op_type.to_string());
                        }
                        
                    }
                    node_data_map.insert({current, nd});
                }
                else if(child_size == 3 && visited) {
                    std::cout << "This is a 3-child node." << std::endl;
                    NodeData& nd = node_data_map[current];
                    for(size_t i = 0; i < num_iterations; i++) {
                        auto & sim_data_1 = node_data_map[children[0]].get_simulation_data();
                        auto & sim_data_2 = node_data_map[children[1]].get_simulation_data();
                        auto & sim_data_3 = node_data_map[children[2]].get_simulation_data();
                        assert(sim_data_1.size() == num_iterations && sim_data_2.size() == num_iterations && sim_data_3.size() == num_iterations);

                        auto btor_child_1 = sim_data_1[i];
                        auto btor_child_2 = sim_data_2[i];
                        auto btor_child_3 = sim_data_3[i];
                        //FIXME: whether to extend bit width or not
                        auto btor_child_1_fix_width = btor_bv_uext(&btor_child_1, 128 - btor_child_1.width);
                        auto btor_child_2_fix_width = btor_bv_uext(&btor_child_2, 128 - btor_child_2.width);
                        auto btor_child_3_fix_width = btor_bv_uext(&btor_child_3, 128 - btor_child_3.width);
                        
                        if(op_type.prim_op == PrimOp::Ite) {
                            cout << "Ite" << endl;
                            auto current_val = btor_bv_ite(btor_child_1_fix_width, btor_child_2_fix_width, btor_child_3_fix_width);
                            nd.add_data(*current_val);
                        }

                    }
                }
               


                else {
                    throw NotImplementedException("Unsupported operator type2: " + op_type.to_string() + " with child size " + std::to_string(child_size));
                }
            //end simulation
            node_stack.pop();
            }
        }
    }
    


    return 0;
}