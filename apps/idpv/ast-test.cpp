#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smtlib_reader.h"

using namespace smt;
using namespace std;
using namespace wasim;

// // find ast nodes
// void traverse_term(const Term &term, std::unordered_set<std::string> &visited_nodes) {
//     if (visited_nodes.find(term->to_string()) != visited_nodes.end()) {
//         return;
//     }

//     visited_nodes.insert(term->to_string());

//     std::cout << "------Child Term: " << term->to_string() << std::endl;
//     std::cout << std::endl;

//     for (auto child : *term) {
//         traverse_term(child, visited_nodes);
//     }
// }

std::unordered_set<Term> traverse_and_collect_terms(const Term &term, std::unordered_set<std::string> &visited_nodes) {
    std::unordered_set<Term> collected_terms;

    if (visited_nodes.find(term->to_string()) != visited_nodes.end()) {
        return collected_terms;
    }

    visited_nodes.insert(term->to_string());
    collected_terms.insert(term); 

    for (auto child : *term) {
        auto child_terms = traverse_and_collect_terms(child, visited_nodes);
        collected_terms.insert(child_terms.begin(), child_terms.end());
    }

    return collected_terms;
}

int main() {
    SmtSolver solver = BoolectorSolverFactory::create(false);

    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser("../design/idpv-test/div_case/suoglu_div.btor2", sts);
    std::cout << "Trans: " << sts.trans()->to_string() << std::endl;

    std::unordered_set<std::string> visited_nodes;
    std::unordered_set<Term> all_terms;

    // for (auto node = sts.trans()->begin(); node != sts.trans()->end(); node++) {
    //     // find_and_check(*node, solver, visited_nodes);
    //     traverse_term(*node, visited_nodes);
    // }

    for (auto node = sts.trans()->begin(); node != sts.trans()->end(); node++) {
        auto collected_terms = traverse_and_collect_terms(*node, visited_nodes);
        all_terms.insert(collected_terms.begin(), collected_terms.end());
    }

    for (auto node1 = all_terms.begin(); node1 != all_terms.end(); ++node1) {
        for (auto node2 = std::next(node1); node2 != all_terms.end(); ++node2) {
            Term term1 = *node1;
            Term term2 = *node2;

            // std::cout<< term1->get_sort()<<std::endl;
            // std::cout<< term2->get_sort()<<std::endl;
            
            if (term1 != term2 && term1->get_sort() == term2->get_sort()) {
                Term eq_term = solver->make_term(Equal, term1, term2);
                solver->assert_formula(eq_term);
                auto result = solver->check_sat();
                
                if (result.is_sat()) {
                    std::cout << "Terms are equivalent:\n";
                    std::cout << "Term 1: " << term1->to_string() << "\n";
                    std::cout << "Term 2: " << term2->to_string() << "\n";
                    std::cout << "--------------------------------------\n";
                }
            }
        }
    }

    return 0;
}