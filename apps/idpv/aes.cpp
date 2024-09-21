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
    solver->assert_formula(not_equal_term);
    if (solver->check_sat().is_unsat()) {
        cout << "These two terms " << var1->to_string() << " and " << var2->to_string() << " are equal" << endl;
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

    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser1("../design/idpv-test/aes_case/aes_all/aes_all_one_round.btor2", sts);
    cout << "-------" << endl;
    BTOR2Encoder btor_parser2("../design/idpv-test/aes_case/AES-Verilog/AES_Verilog_one_round.btor2", sts);
    cout << "-------" << endl;

    // cout << sts.trans()->to_string() << endl;

    smt::UnorderedTermSet free_symbols;
    get_free_symbols(sts.trans(), free_symbols);

    for (const auto& term : free_symbols) {
        cout << "Free symbol: " << term->to_string() << endl;
    }

    //for AES-Verilog
    Term in_term = nullptr;
    Term key128_term = nullptr;

    //for aes_all
    Term key_term = nullptr;
    Term state_term = nullptr;

    for (const auto& term : sts.trans()){ 
        std::string term_str = term->to_string();
        if (term_str == "in"){
            in_term = term;
            cout<< "in" << endl;
        }else if(term_str == "key128"){
            key128_term = term;
            cout<< "key128" << endl;
        }else if(term_str == "key"){
            key_term = term;
        }else if(term_str == "state"){
            state_term = term;
        }

        if (in_term && key128_term && key_term && state_term) {
            break;
        }
    }

    //random input for num_iteration times
    srand(static_cast<unsigned int>(time(0)));
    int num_iterations = 1; 

     for (int i = 0; i < num_iterations; ++i) {
        int64_t in_var = rand() % 100 + 1; 
        int64_t key128_var = rand() % 100 + 1;  
        int64_t key_var = rand() % 100 + 1;  
        int64_t state_var = rand() % 100 + 1;  

        if (!in_term) {
            cerr << "Error: in_term is null." << endl;
            return EXIT_FAILURE;
        }


        auto in_assumption = solver->make_term(in_var, in_term->get_sort());//Segmentation fault
        auto key128_assumption = solver->make_term(key128_var, key128_term->get_sort());
        auto key_assumption = solver->make_term(key_var, key_term->get_sort());
        auto state_assumption = solver->make_term(state_var, state_term->get_sort());

        Term assumption_equal_in = solver->make_term(smt::Equal, in_term, in_assumption);
        Term assumption_equal_key128 = solver->make_term(smt::Equal, key128_term, key128_assumption);
        Term assumption_equal_key = solver->make_term(smt::Equal, key_term, key_assumption);
        Term assumption_equal_state = solver->make_term(smt::Equal, state_term, state_assumption);

        TermVec assumptions{assumption_equal_in, assumption_equal_key128, \
                            assumption_equal_key, assumption_equal_state};

        auto mid_result = solver->check_sat_assuming(assumptions);
        if(mid_result.is_sat()){
            cout << "------maybe equal------" << endl;
        }

        std::unordered_map<Term, NodeData> node_data_map;
        traverse_and_collect_terms(sts.trans(), solver, node_data_map);
        std::unordered_map<std::string, std::vector<Term>> value_term_map;
        for (const auto&  [term, data] : node_data_map) {
            Term value = solver->get_value(term);
            std::string value_term = value->to_string(); // value 对应的 term
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
                        term_merge_map[other_term] = term; // merge into one term
                        cout << "Merge term: " << other_term->to_string() << " with existing term: " << term->to_string() << endl;
                        break;
                    }
                }

            }
        }
       
    }





    return 0;
}
