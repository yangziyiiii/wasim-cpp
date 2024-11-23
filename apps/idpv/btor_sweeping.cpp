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

#include "btor_sweeping.h"

using namespace smt;
using namespace std;
using namespace wasim;

struct NodeData
{
    Term term;  // will be nullptr if it is for a term with array sort
    uint64_t bit_width;
    std::vector<std::string> simulation_data;

    NodeData() : term(nullptr), bit_width(0) {}

    NodeData(Term t, uint64_t bw) : term(t), bit_width(bw) {}
};

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

    operator gmp_randstate_t &() { return state; }
};


std::chrono::time_point<std::chrono::high_resolution_clock> last_time_point;
void print_time() {
    auto now = std::chrono::high_resolution_clock::now();
    auto elapsed_time = std::chrono::duration_cast<std::chrono::milliseconds>(now - last_time_point).count();
    last_time_point = now;  // Update last time point
    cout << "[" << elapsed_time << " ms]  ";
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

    //random n ite sim_data for the input 
    GmpRandStateGuard rand_guard;
    int num_iterations = 10;

    auto &a_key_data = node_data_map[a_key_term];
    auto &a_input_data = node_data_map[a_input_term];
    auto &b_key_data = node_data_map[b_key_term];
    auto &b_input_data = node_data_map[b_input_term];

    for (int i = 0; i < num_iterations; ++i) {
        mpz_t key_mpz, input_mpz;
        rand_guard.random_128(key_mpz);
        rand_guard.random_128(input_mpz);

        // Use RAII for GMP strings
        unique_ptr<char, void (*)(void *)> key_str(mpz_get_str(NULL, 10, key_mpz), free);
        unique_ptr<char, void (*)(void *)> input_str(mpz_get_str(NULL, 10, input_mpz), free);

        mpz_clear(key_mpz);
        mpz_clear(input_mpz);

        //store sim data in NodeData
        a_key_data.simulation_data.push_back(key_str.get());
        a_input_data.simulation_data.push_back(input_str.get());
        b_key_data.simulation_data.push_back(key_str.get());
        b_input_data.simulation_data.push_back(input_str.get());
       
    }  // end of simulation

    cout << a_input_data.simulation_data.size() << endl;
    cout << b_input_data.simulation_data.size() << endl;
    cout << a_key_data.simulation_data.size() << endl;
    cout << b_key_data.simulation_data.size() << endl;

    for(size_t i = 0; i < num_iterations; i++) {
        cout << a_input_data.simulation_data[i] << endl;
        cout << b_input_data.simulation_data[i] << endl;
        cout << a_key_data.simulation_data[i] << endl;
        cout << b_key_data.simulation_data[i] << endl;
        cout << endl;
    }
    
 

    //start post order traversal
    std::stack<std::pair<Term,bool>> node_stack;
    node_stack.push({root,false});
    
    while(!node_stack.empty()) {
        auto & [current,visited] = node_stack.top();

        // cout << "term sort : " << current->get_sort() << endl;
        // auto current_str = current->to_string();
        // auto current_bv = btor_bv_char_to_bv(current_str.data());
        // cout << "current_bv->width: " << current_bv->width << endl;
        // cout << "current sort width: " << current->get_sort()->get_width() << endl;

        if (node_data_map.find(current) != node_data_map.end()) {
            node_stack.pop();
            continue;
        }

        if(!visited) {
            // push all children onto stack
            for(Term child : current) {
                node_stack.push({child,false});
            }
            visited = true;
        } else {
            if(current->is_value()){ //constant
                auto current_str = current->to_string();
                auto current_bv = btor_bv_char_to_bv(current_str.data()); // Btor Bit Vector Type

                if(!current_str.empty() && current_str.find("#b") == 0) {
                    current_str = current_str.substr(2);
                }
               
                auto node_bv_hash = btor_bv_hash(current_bv);
                if(hash_term_map.find(node_bv_hash) == hash_term_map.end()){
                    hash_term_map.insert({node_bv_hash, {current}});
                } else {
                    hash_term_map[node_bv_hash].push_back(current);
                }

                auto node_data = btor_bv_to_char(current_bv);
                
                NodeData nd(current, current->get_sort()->get_width());

                //FIXME: why are they different?
                // cout << "current_bv->width: " << current_bv->width << endl;
                // cout << "current sort width: " << current->get_sort()->get_width() << endl;
                
                for (int i = 0; i < num_iterations; ++i) {
                    nd.simulation_data.push_back(node_data);
                }
                cout << "constant data size: " << nd.simulation_data.size() << endl;
                node_data_map.insert({current, nd});
                btor_bv_free(current_bv);
            }

            else if(current->is_symbol()) { // variants only for leaf nodes
                cout << "This is leaf node" << endl;
                for(size_t i = 0; i < num_iterations; i++) {
                    if(current == a_key_term) {
                       node_data_map[current].simulation_data.push_back(a_key_data.simulation_data[i]);
                    }
                    else if(current == a_input_term) {
                        node_data_map[current].simulation_data.push_back(a_input_data.simulation_data[i]);
                    }
                    else if(current == b_key_term) {
                        node_data_map[current].simulation_data.push_back(b_key_data.simulation_data[i]);
                    }
                    else if(current == b_input_term) {
                        node_data_map[current].simulation_data.push_back(b_input_data.simulation_data[i]);
                    }
                    else {
                        throw std::runtime_error("Unexpected term in leaf node");
                    }
                }
                cout << "leaf node data size: " << node_data_map[current].simulation_data.size() << endl;
            }

            else{ // compute simulation data for current node
                auto op_type = current->get_op();
                TermVec children(current->begin(), current->end());
                auto child_size = children.size();
                cout << "children size: " << child_size << endl;

                if(child_size == 2 && visited) {
                    std::cout << "This is a 2-child node." << std::endl;
                    NodeData nd(current, current->get_sort()->get_width());

                    for(size_t i = 0; i < num_iterations; i++) {
                        auto & sim_data_1 = node_data_map[children[0]].simulation_data;
                        auto & sim_data_2 = node_data_map[children[1]].simulation_data;
                        assert(sim_data_1.size() == num_iterations);
                        assert(sim_data_2.size() == num_iterations);

                        auto btor_child_1 = btor_bv_char_to_bv(sim_data_1[i].data());
                        auto btor_child_2 = btor_bv_char_to_bv(sim_data_2[i].data());

                        if(btor_child_1->width == btor_child_2->width) {
                            if(op_type == BVAdd) {
                                cout << "BVAdd" << endl;
                                auto current_val_btor = btor_bv_add(btor_child_1, btor_child_2);
                                auto current_val = btor_bv_to_char(current_val_btor);
                                nd.simulation_data.push_back(current_val);
                                btor_bv_free(current_val_btor);
                            }
                            else if(op_type == BVAnd) {
                                cout << "BVAnd" << endl;
                                auto current_val_btor = btor_bv_and(btor_child_1, btor_child_2);
                                auto current_val = btor_bv_to_char(current_val_btor);
                                nd.simulation_data.push_back(current_val);
                                btor_bv_free(current_val_btor);
                            }
                            else {
                                throw NotImplementedException("Unsupported operator type" + op_type.to_string());
                            }
                        }
                        btor_bv_free(btor_child_1);
                        btor_bv_free(btor_child_2);
                    }
                    node_data_map.insert({current, nd});
                }
                else if(child_size == 1 && visited) {
                    std::cout << "This is a 1-child node." << std::endl;
                    NodeData nd(current, current->get_sort()->get_width());
                    
                    for(size_t i = 0; i < num_iterations; i++) {
                        auto & sim_data = node_data_map[children[0]].simulation_data;
                        cout << sim_data.size() << endl; 
                        assert(sim_data.size() == num_iterations); //FIXME: 
                        auto btor_child = btor_bv_char_to_bv(sim_data[i].data());

                        auto btor_child_hash = btor_bv_hash(btor_child);
                        if(hash_term_map.find(btor_child_hash) == hash_term_map.end()){
                            hash_term_map.insert({btor_child_hash, {current}});
                        } else {
                            hash_term_map[btor_child_hash].push_back(current);
                        }

                        if(op_type == BVNot) {
                            auto current_val_btor = btor_bv_not(btor_child);
                            auto current_val = btor_bv_to_char(current_val_btor);
                            nd.simulation_data.push_back(current_val);
                            btor_bv_free(current_val_btor);
                        }
                        else {
                            throw NotImplementedException("Unsupported operator type" + op_type.to_string());
                        }
                        btor_bv_free(btor_child);
                    }
                    node_data_map.insert({current, nd});
                }
                else {
                    throw NotImplementedException("Unsupported operator type: " + op_type.to_string() + " with child size " + std::to_string(child_size));
                }
            //end simulation
            node_stack.pop();
            }
        }
    }
    return 0;
}


// void collect_terms(const Term & term, std::unordered_map<Term, NodeData> & node_data_map)
// {
//     if (!term) {
//         throw std::invalid_argument("Null term provided to collect_terms");
//     }

//     std::unordered_set<Term> visited_nodes;
//     std::stack<Term> node_stack;
//     node_stack.push(term);

//     while (!node_stack.empty()) {
//         Term current_term = node_stack.top();
//         node_stack.pop();
//         if (visited_nodes.find(current_term) != visited_nodes.end())
//             continue;

//         // early pruning
//         if (current_term->is_value() || current_term->is_symbol()
//             || (current_term->get_op().is_null()
//             && !current_term->is_symbolic_const())) {
//             // Add sort-based pruning
//             Sort s = current_term->get_sort();
//             if (s->get_sort_kind() == ARRAY) {
//                 continue;  // Skip array terms early
//             }
//             continue;
//         }

//         visited_nodes.insert(current_term);
//         auto res = node_data_map.emplace(current_term, NodeData::from_term(current_term));
//         assert(res.second);

//         if (res.second) {  // Only process children if this is a new term
//             for (auto child : current_term) {
//                 if (child) {
//                 node_stack.push(child);
//                 }
//             }
//         }
//     }
// }

// void collect_termdata(SmtSolver & solver, std::unordered_map<Term, NodeData> & node_data_map)
// {
//     for (auto & term_data_pair : node_data_map) {
//         term_data_pair.second.extend_val(solver);
//     }
// }

// class GmpRandStateGuard
// {
//     gmp_randstate_t state;

//     public:
//     GmpRandStateGuard()
//     {
//         gmp_randinit_default(state);
//         gmp_randseed_ui(state, time(NULL));
//     }

//     ~GmpRandStateGuard() { gmp_randclear(state); }

//     void random_128(mpz_t & rand_num)
//     {
//         mpz_init2(rand_num, 128);
//         mpz_urandomb(rand_num, state, 128);
//     }

//     operator gmp_randstate_t &() { return state; }
// };

// void post_order_traversal(const Term& term, std::vector<Term>& post_order_list) {
//     std::stack<Term> node_stack;
//     std::stack<Term> output_stack;
//     std::unordered_set<Term> visited;

//     node_stack.push(term);
//     while(!node_stack.empty()){
//         Term current = node_stack.top();

//         if( current->is_symbol() || 
//             current->is_value() || 
//             (current->get_op().is_null() && !current->is_symbolic_const()) ||
//             current -> get_sort() -> get_sort_kind() == ARRAY){
//             node_stack.pop();
//         }
        
//         node_stack.pop();
//         output_stack.push(current);
//         visited.insert(current);

//         for(auto child : current){
//             if(child && visited.find(child) == visited.end())
//                 node_stack.push(child);
//         }
//     }

//     while(!output_stack.empty()){
//         Term current = output_stack.top();
//         output_stack.pop();
//         post_order_list.push_back(current);
//     }
// }


// std::unordered_map<Term, NodeData> node_data_map;
    // collect_terms(root, node_data_map);

    // //post order traversal
    // std::vector<Term> post_order_list;
    // post_order_traversal(root, post_order_list);
    // print_time();
    // cout << "post order traversal size: " << post_order_list.size() << endl;

    // // simulation loop
    // GmpRandStateGuard rand_guard;
    // int num_iterations = 1;//FIXME:
    // for (int i = 0; i < num_iterations; ++i) {
    //     print_time();
    //     cout << "Running " << i + 1 << " simulation iteration...\n";
    //     solver->push(); // push for each iteration - context level 2
    //     mpz_t key_mpz, input_mpz;
    //     rand_guard.random_128(key_mpz);
    //     rand_guard.random_128(input_mpz);

    //     // Use RAII for GMP strings
    //     unique_ptr<char, void (*)(void *)> key_str(mpz_get_str(NULL, 10, key_mpz), free);
    //     unique_ptr<char, void (*)(void *)> input_str(mpz_get_str(NULL, 10, input_mpz), free);

    //     auto input_val = solver->make_term(key_str.get(), a_key_term->get_sort());
    //     auto key_val = solver->make_term(input_str.get(), a_input_term->get_sort());

    //     TermVec assumptions{ solver->make_term(Equal, a_key_term, key_val),
    //                         solver->make_term(Equal, a_input_term, input_val),
    //                         solver->make_term(Equal, b_key_term, key_val),
    //                         solver->make_term(Equal, b_input_term, input_val) };
    //     auto check_result = solver->check_sat_assuming(assumptions);
    //     if (!check_result.is_sat()) {
    //         throw std::runtime_error("Unexpected UNSAT result during simulation");
    //     }

    //     collect_termdata(solver, node_data_map);
    //     solver->pop();  // Restore to base context - context level 1

    //     mpz_clear(key_mpz);
    //     mpz_clear(input_mpz);
    // }  // end of simulation
    // cout << "Simulation complete.\n";

    // print_time();
    // cout << "node_data_map size : " << node_data_map.size() << endl;

    // solver->push(); // save the final state - context level 2
    // solver->assert_formula(solver->make_term(smt::Equal, a_key_term, b_key_term));
    // solver->assert_formula(solver->make_term(smt::Equal, a_input_term, b_input_term));

    // std::unordered_map<Term, Term> substitution_map;