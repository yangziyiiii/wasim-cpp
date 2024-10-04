#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smtlib_reader.h"
#include "smt-switch/utils.h"

#include <random>
#include <cstdlib>
#include <ctime> 
#include <iostream>

using namespace smt;
using namespace std;
using namespace wasim;

struct NodeData {
    Term term;
    uint32_t bit_width;
    std::vector<std::string> simulation_data;

    private:
        NodeData(Term t, uint32_t bw, std::vector<std::string>&& sim_data)
            : term(t), bit_width(bw), simulation_data(sim_data) {}

    public:
        NodeData() : term(nullptr), bit_width(0), simulation_data() {}

    static NodeData get_simulation_data(const Term& term, SmtSolver& solver) {
        Term value = solver->get_value(term);
        uint32_t bit_width = value->get_sort()->get_width();
        std::vector<std::string> simulation_data;
        simulation_data.push_back(value->to_string());

        return NodeData(term, bit_width, std::move(simulation_data));
    }
};

void traverse_and_collect_terms(const Term &term, SmtSolver& solver, std::unordered_map<Term, NodeData>& node_data_map) {
    std::unordered_set<Term> visited_nodes;
    std::stack<Term> node_stack;
    node_stack.push(term);

    while (!node_stack.empty()) {
        Term current_term = node_stack.top();
        node_stack.pop();

        if (visited_nodes.find(current_term) != visited_nodes.end()) {
            continue;
        }

        visited_nodes.insert(current_term);
        node_data_map.emplace(current_term, NodeData::get_simulation_data(current_term, solver));

        for (auto child : *current_term) {
            node_stack.push(child);
        }
    }
}

bool compare_terms(const Term& var1, const Term& var2, SmtSolver& solver) {
    Term not_equal_term = solver->make_term(Not, solver->make_term(smt::Equal, var1, var2));
    TermVec not_vec = {not_equal_term};
    auto res = solver->check_sat_assuming(not_vec);    

    if (res.is_unsat()) {
        return true;
    }else{
        return false;
    }
}

int main() {
    SmtSolver solver = BoolectorSolverFactory::create(false);
    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    cout << "-------------- AES-Verilog one round --------------" << endl;
    cout << "---------------------------------------------------" << endl;
    TransitionSystem sts1(solver);
    BTOR2Encoder btor_parser1("../design/idpv-test/aes_case/AES_TOP.btor2", sts1, "a::");
    auto a_key_term = sts1.lookup("a::key");
    auto a_input_term = sts1.lookup("a::datain");
    auto a_output_term = sts1.lookup("a::finalout");

    std::cout << "a_key:" << a_key_term->to_string() << std::endl;
    std::cout << "a_input:" << a_input_term->to_string() << std::endl;
    std::cout << "a_output:" << a_output_term->to_string() << std::endl;

    TransitionSystem sts2(solver);
    BTOR2Encoder btor_parser2("../design/idpv-test/aes_case/AES_Verilog.btor2", sts2, "b::");

    auto b_key_term = sts2.lookup("b::key");
    auto b_input_term = sts2.lookup("b::in");
    auto b_output_term = sts2.lookup("b::out");    

    std::cout << "b_key:" << b_key_term->to_string() << std::endl;
    std::cout << "b_input:" << b_input_term->to_string() << std::endl;
    std::cout << "b_output:" << b_output_term->to_string() << std::endl;

    solver->assert_formula( sts1.init() );
    solver->assert_formula( sts2.init() );
    for (const auto & c : sts1.constraints())
        solver->assert_formula(c.first);
    for (const auto & c : sts2.constraints())
        solver->assert_formula(c.first);

    solver->assert_formula(solver->make_term(Equal, a_key_term, b_key_term));
    solver->assert_formula(solver->make_term(Equal, a_input_term, b_input_term));
    solver->assert_formula(solver->make_term(Not, solver->make_term(Equal, a_output_term, b_output_term)));

    // TODO:the result is SAT, there must be something wrong here!
    std::cout << "Checking..." << std::endl;
    auto r = solver->check_sat();
    std::cout << r.to_string() << std::endl;

    
    /*
    //random input for num_iteration times
    srand(static_cast<unsigned int>(time(0)));
    int num_iterations = 100; 

    for (int i = 0; i < num_iterations; ++i) {
        int64_t in_var = rand() % 100 + 1; 
        int64_t key128_var = rand() % 100 + 1;  

        auto in_assumption = solver->make_term(in_var, in_term->get_sort());//FIXME: Segmentation fault
        auto key128_assumption = solver->make_term(key128_var, key128_term->get_sort());
       
        Term assumption_equal_in = solver->make_term(smt::Equal, in_term, in_assumption);
        Term assumption_equal_key128 = solver->make_term(smt::Equal, key128_term, key128_assumption);

        TermVec assumptions{assumption_equal_in, assumption_equal_key128};

        auto mid_result = solver->check_sat_assuming(assumptions);
        if(mid_result.is_sat()){
            cout << "-------------maybe equal-----------" << endl;
        }else{
            cerr << "---------------unsat------------" << endl;
            break;
        }

        std::unordered_map<Term, NodeData> node_data_map;
        traverse_and_collect_terms(sts1.trans(), solver, node_data_map);
        std::unordered_map<std::string, std::vector<Term>> value_term_map;
        for (const auto&  [term, data] : node_data_map) {
            Term value = solver->get_value(term);
            std::string value_term = value->to_string(); // value -> term
            value_term_map[value_term].push_back(term);
        }

        std::unordered_map<Term,Term> term_merge_map;
        for (const auto& entry : value_term_map) {
            const vector<Term>& term_list = entry.second;

            for (const auto& term : term_list) {
                auto it = term_merge_map.find(term);
                if (it != term_merge_map.end()) {
                    continue;
                }

                for (const auto& other_term : term_list) {
                    if (term != other_term && compare_terms(term, other_term, solver)) {
                        // term_merge_map[other_term] = term; 
                        // TODO: merge into one term
                        cout << "Merge term: " << other_term->to_string() << " with existing term: " << term->to_string() << endl;
                        break;
                    }
                }

            }
        }
       
    }
    */

    // cout << "-------------- AES-128-Bit-Verilog one round --------------" << endl;
    // cout << "-----------------------------------------------------------" << endl;

    // TransitionSystem sts2(solver);//for AES-128-Bit-Verilog
    // BTOR2Encoder btor_parser2("../design/idpv-test/aes_case/AES-128-Bit-Verilog/aescipher_one_cycle.btor2", sts2);
    // smt::UnorderedTermSet free_symbols_2;
    // get_free_symbols(sts2.trans(), free_symbols_2);

    // for(auto const &str : free_symbols_2){
    //     cout << str->to_string() << endl;
    // }

    // //for AES-128-Bit-Verilog
    // Term datain_term = nullptr;
    // Term key_term = nullptr;




    return 0;
}

