// #include <chrono>
// #include "assert.h"
// #include "config/testpath.h"
// #include "frontend/btor2_encoder.h"
// #include "framework/symsim.h"
// #include "framework/ts.h"
// #include "smt-switch/boolector_factory.h"
// #include "smt-switch/smtlib_reader.h"
// #include "smt-switch/utils.h"
// #include "smt-switch/identity_walker.h"
// #include "smt-switch/substitution_walker.h"

// #include <gmp.h>
// #include <gmpxx.h>
// #include <queue>
// #include <thread>
// #include <mutex>
// #include <vector>
// #include <future>

// using namespace smt;
// using namespace std;
// using namespace wasim;


// std::mutex equal_pairs_mutex;
// std::mutex substitution_map_mutex;
// std::mutex solver_mutex;


// template <typename T, typename... Rest>
// inline void hashCombine(std::size_t &seed, T const &v, Rest &&... rest) {
//     std::hash<T> hasher;
//     seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
//     (int[]){0, (hashCombine(seed, std::forward<Rest>(rest)), 0)...};
// }

// struct NodeData{
//     Term term; // will be nullptr if it is for a term with array sort
//     uint64_t bit_width;
//     std::vector<std::string> simulation_data;

//     NodeData() : term(nullptr), bit_width(0) {}

//     private:
//         NodeData(Term t, uint64_t bw)
//             : term(t), bit_width(bw) {}

//     public:
//         void extend_val(SmtSolver& solver) {
//             if (term == nullptr)
//                 return; // array

//             Term value = solver->get_value(term);
//             auto valstr = value->to_string();
//             if (valstr == "true")
//                 valstr = "#b1";
//             else if (valstr == "false")
//                 valstr = "#b0";
//             // maybe other format conversions?
//             simulation_data.push_back(valstr);
//         }

//         size_t hash() const {
//             size_t hash_val = 0;
//             for (const auto & v : simulation_data) {
//                 // hash_val ^= (hash_val << 6) + (hash_val >> 2) + 0x9e3779b9 + std::hash<std::string>{} (v);
//                 hashCombine(hash_val, v);
//             }
//             return hash_val;
//         }

//         bool operator==(const NodeData& other) const {
//             if (term == nullptr)
//                 return false; // for array
//             return simulation_data == other.simulation_data;
//         }

//         static NodeData from_term(const Term& term) {
//             SortKind sk = term->get_sort()->get_sort_kind();
//             switch (sk) {
//                 case ARRAY:
//                     return NodeData(nullptr, 0);
//                 case BV:
//                     return NodeData(term, term->get_sort()->get_width());
//                 case BOOL:
//                     return NodeData(term, 1);
//                 default:
//                     throw std::invalid_argument("Unsupported sort: " + term->get_sort()->to_string());
//             }
//         }
        
// };

// void collect_terms(const Term &term, std::unordered_map<Term, NodeData>& node_data_map ) {
//     if (!term) {
//         throw std::invalid_argument("Null term provided to collect_terms");
//     }

//     std::unordered_set<Term> visited_nodes;
//     std::stack<Term> node_stack;
//     node_stack.push(term);

//     while (!node_stack.empty()) {
//         Term current_term = node_stack.top();
//         node_stack.pop();
//         if (visited_nodes.find(current_term) != visited_nodes.end()) {
//             continue;
//         }
//         visited_nodes.insert(current_term);
//         auto res = node_data_map.emplace(current_term, NodeData::from_term(current_term));
//         assert (res.second);
        
//         for (auto child : current_term) {
//             if (child) {  // Ensure child is not null
//                 node_stack.push(child);
//             }
//         }
//     }
// }

// void collect_termdata(SmtSolver& solver, std::unordered_map<Term, NodeData>& node_data_map ) {
//     for (auto & term_data_pair : node_data_map) {
//         term_data_pair.second.extend_val(solver);
//     }
// }

// bool compare_terms(const Term& var1, const Term& var2, SmtSolver& solver) {
//     if (!var1 || !var2) {
//         return false;
//     }
//     try {
//         TermVec not_equal_term = {solver->make_term(Not, solver->make_term(Equal, var1, var2))};
//         auto res = solver->check_sat_assuming(not_equal_term);
//         return res.is_unsat();
//     } catch (const std::exception& e) {
//         std::cerr << "Error comparing terms: " << e.what() << std::endl;
//         return false;
//     }
// }

// // RAII wrapper for GMP random state
// class GmpRandStateGuard {
//     gmp_randstate_t state;

// public:
//     GmpRandStateGuard() {
//         gmp_randinit_default(state);
//         gmp_randseed_ui(state, time(NULL));
//     }

//     ~GmpRandStateGuard() {
//         gmp_randclear(state);
//     }

//     void random_128(mpz_t& rand_num) {
//         mpz_init2(rand_num, 128);
//         mpz_urandomb(rand_num, state, 128);
//     }

//     operator gmp_randstate_t&() { return state; }
// };

// class DepthWalker : public IdentityWalker
// {
// public:
//     DepthWalker(const SmtSolver &solver, unordered_map<Term, int> &node_depth_map)
//         : IdentityWalker(solver, true), node_depth_map_(node_depth_map) {}

// protected:
//     virtual WalkerStepResult visit_term(Term &term) override
//     {
//         if (node_depth_map_.find(term) != node_depth_map_.end()) {
//             return Walker_Skip;
//         }

//         int max_child_depth = -1;
//         for (const auto &child : term)
//         {
//             auto it = node_depth_map_.find(child);
//             if (it != node_depth_map_.end())
//             {
//                 max_child_depth = max(max_child_depth, it->second);
//             }
//         }
        
//         node_depth_map_[term] = max_child_depth + 1;
//         return Walker_Continue;
//     }

// private:
//     unordered_map<Term, int> &node_depth_map_;
// };


// void process_hash_group(
//     std::pair<size_t, TermVec> &hash_group,
//     const std::unordered_map<Term, NodeData> &node_data_map,
//     const std::unordered_map<Term, int> &node_depth_map,
//     SmtSolver &solver,
//     std::vector<std::pair<Term, Term>> &equal_pairs,
//     smt::UnorderedTermMap &substitution_map) {

//     auto &terms = hash_group.second;

//     std::sort(terms.begin(), terms.end(), [&]( Term &a, Term &b) {
//         return node_depth_map.at(a) < node_depth_map.at(b);
//     });

//     if (terms.size() > 1) {
//         for (size_t i = 0; i < terms.size(); ++i) {
//             const auto &term1 = terms[i];
//             bool substituted = false;

//             for (size_t j = i + 1; j < terms.size(); ++j) {
//                 const auto &term2 = terms[j];

//                 // Check equivalence and sort match
//                 {
//                     std::lock_guard<std::mutex> solver_lock(solver_mutex);
//                     if (node_data_map.at(term1).simulation_data == node_data_map.at(term2).simulation_data 
//                         && term1->get_sort() == term2->get_sort() 
//                         && compare_terms(term1, term2, solver)) {

//                         std::cout << "Equivalent terms found at: " << term1->get_sort()
//                                   << ", hash: " << hash_group.first << std::endl;

//                         {
//                             std::lock_guard<std::mutex> lock(equal_pairs_mutex);
//                             equal_pairs.emplace_back(term1, term2);
//                         }

//                         {
//                             std::lock_guard<std::mutex> lock(substitution_map_mutex);
//                             if (node_depth_map.at(term1) < node_depth_map.at(term2)) {
//                                 substitution_map[term2] = term1;
//                             } else {
//                                 substitution_map[term1] = term2;
//                             }
//                         }

//                         substituted = true;
//                         break;
//                     }
//                 }
//             }

//             if (substituted) break;
//         }
//     }
// }


// int main() {
//     SmtSolver solver = BoolectorSolverFactory::create(false);

//     solver->set_logic("QF_UFBV");
//     solver->set_opt("incremental", "true");
//     solver->set_opt("produce-models", "true");
//     solver->set_opt("produce-unsat-assumptions", "true");

//     TransitionSystem sts1(solver);
//     BTOR2Encoder btor_parser1("../design/idpv-test/aes_case/AES_TOP.btor2", sts1, "a::");

//     auto a_key_term = sts1.lookup("a::key");
//     auto a_input_term = sts1.lookup("a::datain");
//     auto a_output_term = sts1.lookup("a::finalout");

//     TransitionSystem sts2(solver);
//     BTOR2Encoder btor_parser2("../design/idpv-test/aes_case/AES_Verilog.btor2", sts2, "b::");

//     auto b_key_term = sts2.lookup("b::key");
//     auto b_input_term = sts2.lookup("b::in");
//     auto b_output_term = sts2.lookup("b::out");    

//     //Assert constraints
//     solver->assert_formula( sts1.init() );
//     solver->assert_formula( sts2.init() );
//     for (const auto & c : sts1.constraints())
//         solver->assert_formula(c.first);
//     for (const auto & c : sts2.constraints())
//         solver->assert_formula(c.first);

//     if (!a_key_term || !a_input_term || !b_input_term || !b_key_term || !a_output_term || !b_output_term) {
//         throw std::runtime_error("Required terms not found in models");
//     }

//     auto res_ast = solver->make_term(Equal, a_output_term, b_output_term); // move the outer of the loop

//     std::unordered_map<Term, NodeData> node_data_map;
//     collect_terms(res_ast, node_data_map);

//     // simulation iterations below    
//     GmpRandStateGuard rand_guard;

//     int num_iterations = 10;
//     for (int i = 0; i < num_iterations; ++i) {
//         mpz_t key_mpz, input_mpz;
//         rand_guard.random_128(key_mpz);
//         rand_guard.random_128(input_mpz);

//         // Use RAII for GMP strings
//         unique_ptr<char, void(*)(void*)> key_str(mpz_get_str(NULL, 10, key_mpz), free);
//         unique_ptr<char, void(*)(void*)> input_str(mpz_get_str(NULL, 10, input_mpz), free);

//         auto input_val = solver->make_term(key_str.get(), a_key_term->get_sort());
//         auto key_val = solver->make_term(input_str.get(), a_input_term->get_sort());

//         TermVec assumptions{
//             solver->make_term(Equal, a_key_term, key_val),
//             solver->make_term(Equal, a_input_term, input_val),
//             solver->make_term(Equal, b_key_term, key_val),
//             solver->make_term(Equal, b_input_term, input_val)
//         };

//         auto check_result = solver->check_sat_assuming(assumptions);
//         if (!check_result.is_sat()) {
//             throw std::runtime_error("Unexpected UNSAT result during simulation");
//         }

//         collect_termdata(solver, node_data_map);

//         mpz_clear(key_mpz);
//         mpz_clear(input_mpz);
//     } // end of simulation

//     cout << "node_data_map size : " << node_data_map.size() << endl;

//     solver->assert_formula(solver->make_term(smt::Equal, a_key_term, b_key_term));
//     solver->assert_formula(solver->make_term(smt::Equal, a_input_term, b_input_term));

//     std::unordered_map<size_t, TermVec> hash_term_map; // the hash of nodeData

//     for (const auto& entry : node_data_map) {
//         auto entry_first = entry.first;
//         const NodeData& node_data = entry.second;
//         size_t hash_val = node_data.hash();
//         hash_term_map[hash_val].push_back(entry_first);
//     }

//     cout << "hash_term_map size : " << hash_term_map.size() << endl;

//     //define depth using Walker
//     std::unordered_map<Term, int> node_depth_map;
//     DepthWalker depth_walker(solver, node_depth_map);
//     depth_walker.visit(res_ast);
    
//     cout << "node depth size: " << node_depth_map.size() << endl;
//     //  for (const auto& [term, depth] : node_depth_map) {
//     //     std::cout << " Depth: " << depth << std::endl;   
//     // }

//     //comapre and store equal nodes
//     std::vector<std::pair<Term, Term>> equal_pairs;
//     smt::UnorderedTermMap substitution_map;


//     //FIXME: async error
//     std::vector<std::future<void>> futures;
//     for (auto &hash_group : hash_term_map) {
//         futures.emplace_back(std::async(
//             std::launch::async,
//             process_hash_group,
//             std::ref(hash_group),
//             std::cref(node_data_map),
//             std::cref(node_depth_map),
//             std::ref(solver),
//             std::ref(equal_pairs),
//             std::ref(substitution_map)
//         ));
//     }

//     // 等待所有线程完成
//     for (auto &fut : futures) {
//         fut.get();
//     }

//     std::cout << "equal pairs: " << equal_pairs.size() << std::endl;
//     std::cout << "substitution map size: " << substitution_map.size() << std::endl;

//     return 0;
// }