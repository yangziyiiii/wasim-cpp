#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smtlib_reader.h"
#include "smt-switch/utils.h"


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

int main() {
    SmtSolver solver = BoolectorSolverFactory::create(false);

    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser("../design/idpv-test/div_case/suoglu_div.btor2", sts);

    smt::UnorderedTermSet free_symbols;
    get_free_symbols(sts.trans(), free_symbols);

    Term divisor_term = nullptr;
    Term dividend_term = nullptr;
    Term start_term = nullptr;
    Term rst_term = nullptr;
    Term clk_term = nullptr;

    for (const auto& term : free_symbols){ // loop once for all invar
        std::string term_str = term->to_string();
        if (term_str == "divisor"){
            divisor_term = term;
        }else if(term_str == "dividend"){
            dividend_term = term;
        }else if(term_str == "start"){
            start_term = term;
        }else if(term_str == "rst"){
            rst_term = term;
        }

        if (divisor_term && dividend_term && start_term && rst_term) {
            break;
        }
    }

    int64_t divisor_var = 3;
    int64_t dividend_var = 4;
    int64_t start_var = 5;
    int64_t rst_var = 1;


    auto divisor_assumption = solver->make_term(divisor_var, divisor_term->get_sort());
    auto dividend_assumption = solver->make_term(dividend_var, dividend_term->get_sort());
    auto start_assumption = solver->make_term(start_var, start_term->get_sort());
    auto rst_assumption = solver->make_term(rst_var, rst_term->get_sort());

    Term assumption_equal_divisor = solver->make_term(smt::Equal, divisor_term, divisor_assumption);
    Term assumption_equal_dividend = solver->make_term(smt::Equal, dividend_term, dividend_assumption); 
    Term assumption_equal_start = solver->make_term(smt::Equal, start_term, start_assumption); 
    Term assumption_equal_rst = solver->make_term(smt::Equal, rst_term, rst_assumption); 

    TermVec assumptions{assumption_equal_dividend,assumption_equal_divisor,\
        assumption_equal_rst,assumption_equal_start};
    auto result = solver->check_sat_assuming(assumptions);

    if(result.is_sat()){
        cout<< "sat" <<endl;
    }

    std::unordered_map<Term, NodeData> node_data_map;
    traverse_and_collect_terms(sts.trans(), solver, node_data_map);    
    for (const auto& [term, data] : node_data_map) {
        cout << "Term: " << term->to_string() <<endl;
        cout << "Bit Width: " << data.bit_width <<endl;
        cout << "Simulation Data: ";
        for (const auto& str : data.simulation_data) {
            cout << str << endl;
        }
        cout << "-----------------------------------------" << endl;
    }




    

    // for (auto it1 = free_symbols.begin(); it1 != free_symbols.end(); ++it1) {
    //     for (auto it2 = std::next(it1); it2 != free_symbols.end(); ++it2) {
    //         Term var1 = *it1;
    //         Term var2 = *it2;
    //         if(var1->get_sort() == var2->get_sort()){
    //             auto equal_var = solver->make_term(smt::Equal,var1,var2);
    //             Term equality_formula = solver->make_term(Not,equal_var);
    //             solver->assert_formula(equal_var);
    //             if (solver->check_sat().is_unsat()) {
    //                 std::unordered_map<Term, NodeData> node_data_map;
    //                 traverse_and_collect_terms(sts.trans(), solver, node_data_map);

    //                 for (const auto& [term, data] : node_data_map) {
    //                     std::cout << "Term: " << term->to_string() << std::endl;
    //                     std::cout << "Bit Width: " << data.bit_width << std::endl;
    //                     std::cout << "Simulation Data: ";
    //                     for (const auto& str : data.simulation_data) {
    //                         std::cout << str << " ";
    //                     }
    //                     std::cout << std::endl;
    //                 }
    //             }else{
    //                 std::cout << "not equal" << std::endl;
    //             }
    //         }
    //     }
    // }




    return 0;
}
