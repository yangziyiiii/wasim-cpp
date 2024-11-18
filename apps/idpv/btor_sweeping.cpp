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
#include "btor_sweeping.h"

using namespace smt;
using namespace std;
using namespace wasim;

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

    //start post order traversal
    std::stack<Term> node_stack;
    node_stack.push(root);
    std::unordered_map<Term, bool> nodes;
    nodes.insert({root, false});

    while(!node_stack.empty()) {
        Term current = node_stack.top();
        for(Term child : current) {
            if(child){ // 子节点存在，继续向下遍历
                nodes[current] = true;
                if(nodes.find(child) == nodes.end()){
                    node_stack.push(child);
                    nodes.insert({child, false});
                }
            }
            else{ // 子节点不存在，对当前节点进行simulation
                if(child->is_value()) { // 常量
                    //直接获取这个节点的值
                }
                else if(child->is_symbol()) { // 变量
                    //根据节点的op进行simulation
                    if(child->get_op() == BVAdd) {

                    }
                }
            }
        }
    }
    






    
    return 0;

}





// template <typename T, typename... Rest>
// inline void hashCombine(std::size_t & seed, T const & v, Rest &&... rest)
// {
//   std::hash<T> hasher;
//   seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
//   (int[]){ 0, (hashCombine(seed, std::forward<Rest>(rest)), 0)... };
// }


// struct NodeData
// {
//   Term term;  // will be nullptr if it is for a term with array sort
//   uint64_t bit_width;
//   std::vector<std::string> simulation_data;

//   NodeData() : term(nullptr), bit_width(0) {}

//  private:
//   NodeData(Term t, uint64_t bw) : term(t), bit_width(bw) {}

//  public:
//   void extend_val(SmtSolver & solver)
//   {
//     if (term == nullptr) return;  // array

//     static std::string valstr;
//     valstr.clear();
//     Term value = solver->get_value(term);
//     valstr = value->to_string();
//     if (valstr == "true")
//       valstr = "#b1";
//     else if (valstr == "false")
//       valstr = "#b0";
//     simulation_data.push_back(std::move(valstr));
//   }

//   size_t hash() const
//   {
//     if (simulation_data.empty()) {
//       return 0;
//     }

//     size_t hash_val = 0;
//     for (const auto & v : simulation_data) {
//       // Remove any prefix like "#b" before hashing
//       std::string clean_val = v;
//       if (v.substr(0, 2) == "#b") {
//         clean_val = v.substr(2);
//       }
//       hashCombine(hash_val, clean_val);
//     }
//     return hash_val;
//   }

//   bool operator==(const NodeData & other) const
//   {
//     if (term == nullptr) return false;  // for array
//     return simulation_data == other.simulation_data;
//   }

//   static NodeData from_term(const Term & term)
//   {
//     SortKind sk = term->get_sort()->get_sort_kind();
//     switch (sk) {
//       case ARRAY: return NodeData(nullptr, 0);
//       case BV: return NodeData(term, term->get_sort()->get_width());
//       case BOOL: return NodeData(term, 1);
//       default:
//         throw std::invalid_argument("Unsupported sort: " + term->get_sort()->to_string());
//     }
//   }
// };

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