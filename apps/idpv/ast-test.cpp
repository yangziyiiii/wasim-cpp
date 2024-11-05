#include <gmp.h>
#include <gmpxx.h>

#include <chrono>
#include <queue>

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

struct NodeData
{
  Term term;  // will be nullptr if it is for a term with array sort
  uint64_t bit_width;
  std::vector<std::string> simulation_data;

  NodeData() : term(nullptr), bit_width(0) {}

 private:
  NodeData(Term t, uint64_t bw) : term(t), bit_width(bw) {}

 public:
  void extend_val(SmtSolver & solver)
  {
    if (term == nullptr) return;  // array

    static std::string valstr;
    valstr.clear(); // FIXME: could cause thread-safety issues if the code ever becomes multi-threaded.
    Term value = solver->get_value(term);
    valstr = value->to_string();
    if (valstr == "true")
      valstr = "#b1";
    else if (valstr == "false")
      valstr = "#b0";
    simulation_data.push_back(std::move(valstr));
  }

  size_t hash() const
  {
    if (simulation_data.empty()) {
      return 0;
    }

    size_t hash_val = 0;
    for (const auto & v : simulation_data) {
      // Remove any prefix like "#b" before hashing
      std::string clean_val = v;
      if (v.substr(0, 2) == "#b") {
        clean_val = v.substr(2);
      }
      hashCombine(hash_val, clean_val);
    }
    return hash_val;
  }

  bool operator==(const NodeData & other) const
  {
    if (term == nullptr) return false;  // for array
    return simulation_data == other.simulation_data;
  }

  static NodeData from_term(const Term & term)
  {
    SortKind sk = term->get_sort()->get_sort_kind();
    switch (sk) {
      case ARRAY: return NodeData(nullptr, 0);
      case BV: return NodeData(term, term->get_sort()->get_width());
      case BOOL: return NodeData(term, 1);
      default:
        throw std::invalid_argument("Unsupported sort: " + term->get_sort()->to_string());
    }
  }
};

void collect_terms(const Term & term, std::unordered_map<Term, NodeData> & node_data_map)
{
    if (!term) {
        throw std::invalid_argument("Null term provided to collect_terms");
    }

    std::unordered_set<Term> visited_nodes;
    std::stack<Term> node_stack;
    node_stack.push(term);

    while (!node_stack.empty()) {
        Term current_term = node_stack.top();
        node_stack.pop();
        if (visited_nodes.find(current_term) != visited_nodes.end())
            continue;

        // early pruning
        if (current_term->is_value() || current_term->is_symbol()
            || (current_term->get_op().is_null()
            && !current_term->is_symbolic_const())) {
            // Add sort-based pruning
            Sort s = current_term->get_sort();
            if (s->get_sort_kind() == ARRAY) {
                continue;  // Skip array terms early
            }
            continue;
        }

    visited_nodes.insert(current_term);
    auto res =
        node_data_map.emplace(current_term, NodeData::from_term(current_term));
    assert(res.second);

    if (res.second) {  // Only process children if this is a new term
      for (auto child : current_term) {
        if (child) {
          node_stack.push(child);
        }
      }
    }
  }
}

void collect_termdata(SmtSolver & solver, std::unordered_map<Term, NodeData> & node_data_map)
{
    for (auto & term_data_pair : node_data_map) {
        term_data_pair.second.extend_val(solver);
    }
}

using TermPair = std::pair<Term, Term>;
struct TermPairHash
{
  size_t operator()(const TermPair & p) const
  {
    return std::hash<Term>()(p.first) ^ std::hash<Term>()(p.second);
  }
};
std::unordered_map<TermPair, bool, TermPairHash> comparison_cache;

// TODO: Could add term characteristics-based grouping
// struct TermCharacteristics {
//     SortKind sort_kind;
//     uint64_t bit_width;
//     Op op;
// };
// std::unordered_map<TermCharacteristics, TermVec> term_groups;

bool compare_terms(const Term & var1, const Term & var2, SmtSolver & solver)
{
    if (!var1 || !var2) return false;

    TermPair pair(var1, var2);
    auto it = comparison_cache.find(pair);
    if (it != comparison_cache.end()) {
        return it->second;
    }

    try {
        TermVec not_equal_term = { solver->make_term(Not, solver->make_term(Equal, var1, var2)) };
        auto res = solver->check_sat_assuming(not_equal_term);
        bool result = res.is_unsat();
        comparison_cache[pair] = result;
        return result;
    }
    catch (...) {
        return false;
    }
}


// RAII wrapper for GMP random state
class GmpRandStateGuard
{
    gmp_randstate_t state;

    public:
    GmpRandStateGuard()
    {
        gmp_randinit_default(state);
        gmp_randseed_ui(state, time(NULL));
    }

    ~GmpRandStateGuard() { gmp_randclear(state); }

    void random_128(mpz_t & rand_num)
    {
        mpz_init2(rand_num, 128);
        mpz_urandomb(rand_num, state, 128);
    }

    operator gmp_randstate_t &() { return state; }
};

class DepthWalker : public IdentityWalker
{
    public:
        DepthWalker(const SmtSolver & solver, unordered_map<Term, int> & node_depth_map)
            : IdentityWalker(solver, true), node_depth_map_(node_depth_map) {}

    protected:
        virtual WalkerStepResult visit_term(Term & term) override
        {
            if (node_depth_map_.find(term) != node_depth_map_.end()) {
                return Walker_Skip;
            }

            int max_child_depth = -1;
            for (const auto & child : term) {
                auto it = node_depth_map_.find(child);
                if (it != node_depth_map_.end()) {
                    max_child_depth = max(max_child_depth, it->second);
                }
            }

            node_depth_map_[term] = max_child_depth + 1;
            return Walker_Continue;
        }

    private:
    unordered_map<Term, int> & node_depth_map_;
};

int main()
{
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
    solver->assert_formula(sts1.init());
    solver->assert_formula(sts2.init());
    for (const auto & c : sts1.constraints()) solver->assert_formula(c.first);
    for (const auto & c : sts2.constraints()) solver->assert_formula(c.first);

    // Create a base context that we'll reuse
    solver->push(); // context level 1

    if (!a_key_term || !a_input_term || !b_input_term || !b_key_term || !a_output_term || !b_output_term) {
        throw std::runtime_error("Required terms not found in models");
    }

    auto res_ast = solver->make_term(Equal, a_output_term, b_output_term);

    cout << "Starting simulation phase...\n";
    std::unordered_map<Term, NodeData> node_data_map;
    collect_terms(res_ast, node_data_map);

    // simulation iterations below
    GmpRandStateGuard rand_guard;

    int num_iterations = 10;
    // simulation loop
    #pragma omp parallel for
    for (int i = 0; i < num_iterations; ++i) {
        cout << "Running " << i + 1 << " simulation iteration...\n";
        solver->push(); // push for each iteration - context level 2
        mpz_t key_mpz, input_mpz;
        rand_guard.random_128(key_mpz);
        rand_guard.random_128(input_mpz);

        // Use RAII for GMP strings
        unique_ptr<char, void (*)(void *)> key_str(mpz_get_str(NULL, 10, key_mpz), free);
        unique_ptr<char, void (*)(void *)> input_str(mpz_get_str(NULL, 10, input_mpz), free);

        auto input_val = solver->make_term(key_str.get(), a_key_term->get_sort());
        auto key_val = solver->make_term(input_str.get(), a_input_term->get_sort());

        TermVec assumptions{ solver->make_term(Equal, a_key_term, key_val),
                            solver->make_term(Equal, a_input_term, input_val),
                            solver->make_term(Equal, b_key_term, key_val),
                            solver->make_term(Equal, b_input_term, input_val) };
        auto check_result = solver->check_sat_assuming(assumptions);
        if (!check_result.is_sat()) {
            throw std::runtime_error("Unexpected UNSAT result during simulation");
        }

        collect_termdata(solver, node_data_map);

        solver->pop();  // Restore to base context - context level 1

        mpz_clear(key_mpz);
        mpz_clear(input_mpz);
    }  // end of simulation
    cout << "\nSimulation complete.\n";
    //   for (const auto & [term, data] : node_data_map) {
    //     cout << "Term has " << data.simulation_data.size()
    //          << " simulation values\n";
    //   }

    cout << "node_data_map size : " << node_data_map.size() << endl;

    solver->push(); // save the final state - context level 2
    solver->assert_formula(solver->make_term(smt::Equal, a_key_term, b_key_term));
    solver->assert_formula(solver->make_term(smt::Equal, a_input_term, b_input_term));

    cout << "Building hash term map...\n";
    std::unordered_map<size_t, TermVec> hash_term_map;
    //   for (const auto & [hash, terms] : hash_term_map) {
    //     cout << "Hash " << hash << " has " << terms.size() << " terms\n";
    //   }

    cout << "Populating hash term map...\n";
    size_t terms_processed = 0;
    // population loop
    for (const auto & entry : node_data_map) {
        terms_processed++;
        if (terms_processed % 1000 == 0) {
        cout << "Processed " << terms_processed << "/" << node_data_map.size()
            << " terms\n";
        }

        const Term & term = entry.first;
        const NodeData & node_data = entry.second;

    // Skip terms that we know won't be useful
    if (!term || term->get_sort()->get_sort_kind() == ARRAY) {
      continue;
    }

    size_t hash_val = node_data.hash();

    // Debug output for hash values
    if (terms_processed % 1000 == 0) {
      cout << "Term hash: " << hash_val
           << ", simulation data size: " << node_data.simulation_data.size()
           << "\n";
    }

    hash_term_map[hash_val].push_back(term);
    }

    // Debug output for hash distribution
    cout << "\nHash distribution:\n";
    std::map<size_t, size_t> bucket_sizes;
    for (const auto & [hash, terms] : hash_term_map) {
        bucket_sizes[terms.size()]++;
    }

    for (const auto & [size, count] : bucket_sizes) {
        cout << "Buckets with " << size << " terms: " << count << "\n";
    }

    cout << "hash_term_map size : " << hash_term_map.size() << endl;

    cout << "Calculating node depths...\n";
    // define depth using Walker
    std::unordered_map<Term, int> node_depth_map;
    DepthWalker depth_walker(solver, node_depth_map);
    depth_walker.visit(res_ast);

    cout << "node depth size: " << node_depth_map.size() << endl;
    //  for (const auto& [term, depth] : node_depth_map) {
    //     std::cout << " Depth: " << depth << std::endl;
    // }
    cout << "\nStarting term comparison phase...\n";
    // comapre and store equal nodes
    std::vector<std::pair<Term, Term>> equal_pairs;
    smt::UnorderedTermMap substitution_map;

    // FIXME: time consuming
    size_t processed = 0;
    #pragma omp parallel for
    for (auto & hash_group : hash_term_map) {
        processed++;
        if (processed % 10 == 0) {
            cout << "Processed " << processed << "/" << hash_term_map.size()
                << " groups\n";
        }
        auto & terms = hash_group.second;
        // cout << "Processing hash group with " << terms.size() << " terms\n";

        // Skip small groups
        if (terms.size() <= 1) continue;

        for (size_t i = 0; i < terms.size(); ++i) {
            // Sort by depth first
            std::sort(
                terms.begin(), terms.end(), [&](const Term & a, const Term & b) {
                    return node_depth_map[a] < node_depth_map[b];
                });

            for(size_t i = 0; i < terms.size(); ++i) {
                const auto & term1 = terms[i];
                for(size_t j = i + 1; j < terms.size(); ++j) {
                    const auto & term2 = terms[j];
                    if(node_data_map[term1].simulation_data == node_data_map[term2].simulation_data
                        && term1->get_sort() == term2->get_sort()) {
                        if(compare_terms(term1, term2, solver)) {
                            if (node_depth_map[term1] < node_depth_map[term2]) {
                                substitution_map[term2] = term1;
                                solver->substitute(term2, substitution_map);
                            } else {
                                substitution_map[term1] = term2;
                                solver->substitute(term1, substitution_map);
                            }
                            //TODO:
                        }
                    }
                }
            }
        }
    }
    cout << "equal pairs: " << equal_pairs.size() << endl;

    solver->pop(); // restore the final state - context level 2
    solver->pop(); // back to base context
    
    solver->assert_formula(res_ast);
    cout << "Checking final result...\n";
    auto final_result = solver->check_sat();
    std::cout << r.to_string() << std::endl;
    //count time
    auto end_time = std::chrono::high_resolution_clock::now();
    auto elapsed_time = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();
    cout << "Elapsed time: " << elapsed_time / 1000 / 60 << " minutes\n";

    return 0;
}