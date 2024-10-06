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
    // std::vector<std::string> simulation_data;
    std::string simulation_data;

    private:
        NodeData(Term t, uint32_t bw, std::string&& sim_data)
            : term(t), bit_width(bw), simulation_data(sim_data) {}

    public:
        NodeData() : term(nullptr), bit_width(0), simulation_data() {}

    static NodeData get_simulation_data(const Term& term, SmtSolver& solver) {
        Term value = solver->get_value(term);
        uint32_t bit_width = value->get_sort()->get_width();
        // std::vector<std::string> simulation_data;
        // simulation_data.push_back(value->to_string());
        std::string simulation_data = value->to_string();

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
    TermVec not_equal_term = {solver->make_term(Not, solver->make_term(smt::Equal, var1, var2))};
    auto res = solver->check_sat_assuming(not_equal_term);    
    return res.is_unsat();
}

int main() {
    SmtSolver solver = BoolectorSolverFactory::create(false);
    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

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

    std::cout << "Checking..." << std::endl;
    auto r = solver->check_sat();
    std::cout << r.to_string() << std::endl;

    //random input for num_iteration times
    // srand(static_cast<unsigned int>(time(0)));
    // int num_iterations = 100; 

    // for (int i = 0; i < num_iterations; ++i) {
    //     int64_t a_input_var = rand() % 100 + 1;
    //     int64_t a_key_var = rand() % 100 + 1;

    //     auto a_input_assumption = solver->make_term(a_input_var, a_input_term->get_sort());
    //     auto a_key_assumption = solver->make_term(a_key_var, a_key_term->get_sort());
       
    //     Term assumption_equal_a_input = solver->make_term(smt::Equal, a_input_term, a_input_assumption);
    //     Term assumption_equal_a_key = solver->make_term(smt::Equal, a_key_term, a_key_assumption);

    //     TermVec assumptions{assumption_equal_a_input, assumption_equal_a_key};

    //     auto mid_result = solver->check_sat_assuming(assumptions);

    //     for(mid_result.is_sat()){
    //         std::unordered_map<Term, NodeData> node_data_map_a;
    //         traverse_and_collect_terms(sts1.trans(), *solver, node_data_map_a);

    //         std::unordered_map<Term, NodeData> node_data_map_b;
    //         traverse_and_collect_terms(sts2.trans(), *solver, node_data_map_b);
    //     }

        // std::unordered_map<Term, NodeData> node_data_map;


        // traverse_and_collect_terms(sts1.trans(), solver, node_data_map);
        // std::unordered_map<std::string, std::vector<Term>> value_term_map;
        // for (const auto&  [term, data] : node_data_map) {
        //     Term value = solver->get_value(term);
        //     std::string value_term = value->to_string(); // value -> term
        //     value_term_map[value_term].push_back(term);
        // }

        // std::unordered_map<Term,Term> term_merge_map;
        // for (const auto& entry : value_term_map) {
        //     const vector<Term>& term_list = entry.second;

        //     for (const auto& term : term_list) {
        //         auto it = term_merge_map.find(term);
        //         if (it != term_merge_map.end()) {
        //             continue;
        //         }

        //         for (const auto& other_term : term_list) {
        //             if (term != other_term && compare_terms(term, other_term, solver)) {
        //                 // term_merge_map[other_term] = term; 
        //                 // TODO: merge into one term
        //                 cout << "Merge term: " << other_term->to_string() << " with existing term: " << term->to_string() << endl;
        //                 break;
        //             }
        //         }

        //     }
        // }
       
    



    return 0;
}

