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

using namespace smt;
using namespace std;
using namespace wasim;

void post_order_traversal(const Term& term, std::vector<Term>& post_order_list) {
    assert(term != nullptr);

    std::unordered_set<Term> visited_nodes;
    std::stack<Term> node_stack;
    std::stack<Term> output_stack; 

    node_stack.push(term);
    while (!node_stack.empty()) {
        Term current = node_stack.top();
        node_stack.pop();
        output_stack.push(current);
        visited_nodes.insert(current);

        std::vector<Term> children;
        for (auto child : current) {
            if (child && visited_nodes.find(child) == visited_nodes.end()) {
                children.push_back(child);
            }
        }

        for (int i = children.size() - 1; i >= 0; --i) {
            node_stack.push(children[i]);
        }
    }

    while (!output_stack.empty()) {
        Term current = output_stack.top();
        output_stack.pop();
        post_order_list.push_back(current);
    }

}

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
    // SmtSolver solver = BitwuzlaSolverFactory::create(false);

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

    //post order traversal
    std::vector<Term> post_order_list;
    post_order_traversal(root, post_order_list);
    cout << "post order traversal size: " << post_order_list.size() << endl;

    smt::UnorderedTermMap substitution_map;

    for(auto term : post_order_list) {
        //TODO: new simulation method for a term using boolector
    }

    
    return 0;

}