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

    for (auto it1 = free_symbols.begin(); it1 != free_symbols.end(); ++it1) {
        for (auto it2 = std::next(it1); it2 != free_symbols.end(); ++it2) {
            Term var1 = *it1;
            Term var2 = *it2;
            if(var1->get_sort() == var2->get_sort()){
                auto equal_var = solver->make_term(smt::Equal,var1,var2);
                Term equality_formula = solver->make_term(Not,equal_var);
                solver->assert_formula(equal_var);
                if (solver->check_sat().is_unsat()) {
                    std::unordered_map<Term, NodeData> node_data_map;
                    traverse_and_collect_terms(sts.trans(), solver, node_data_map);

                    for (const auto& [term, data] : node_data_map) {
                        std::cout << "Term: " << term->to_string() << std::endl;
                        std::cout << "Bit Width: " << data.bit_width << std::endl;
                        std::cout << "Simulation Data: ";
                        for (const auto& str : data.simulation_data) {
                            std::cout << str << " ";
                        }
                        std::cout << std::endl;
                    }
                }else{
                    std::cout << "not equal" << std::endl;
                }
            }
        }
    }
    return 0;
}
