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

template <typename T, typename... Rest>
inline void hashCombine(std::size_t & seed, T const & v, Rest &&... rest)
{
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
  (int[]){ 0, (hashCombine(seed, std::forward<Rest>(rest)), 0)... };
}

struct Node {
    Term term;
    struct Node *left, *right;
};

Node* newNode(Term term) {
    Node* node = new Node;
    node->term = term;
    node->left = node->right = NULL;
    return node;
}

//FIXME: 
void post_order_traversal(const Term & term, std::vector<Term> & postOrderList) {
    Node* root = newNode(term);
    if(root == NULL)
        throw std::invalid_argument("NULL term provided to post_order_traversal");
    
    std::stack<Node*> node_stack;
    std::unordered_set<Term> visietd_nodes;
    node_stack.push(root);
    Node* prev = NULL;

    while(!node_stack.empty()) {
        auto current = node_stack.top();
        cout << current->term->hash() << endl;
        if (current->term->is_value() || current->term->is_symbol() || ( current->term->get_op().is_null() && !current->term->is_symbolic_const())) {
            Sort s = current->term->get_sort();
            if(s->get_sort_kind() == ARRAY) {
                node_stack.pop();
                delete current;
                continue;
            }
            node_stack.pop();
            delete current;
            continue;
        }

        if(prev == NULL || prev->left == current || prev->right == current) {
            if(current->left)
                node_stack.push(current->left);
            else if(current->right)
                node_stack.push(current->right);
            else {
                node_stack.pop();
                postOrderList.push_back(current->term);
            }
        }
        else if(current->left == prev) {
            if(current->right)
                node_stack.push(current->right);
            else {
                node_stack.pop();
                postOrderList.push_back(current->term);
            }
        }
        else if(current->right == prev) {
            node_stack.pop();
            postOrderList.push_back(current->term);
        }
        prev = current;
    }
    return;
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
    cout << "post order traversal size: " << post_order_list.size() << endl; // 1
    
    return 0;

}