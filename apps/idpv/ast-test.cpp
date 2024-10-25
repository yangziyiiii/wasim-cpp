#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smtlib_reader.h"
#include "smt-switch/utils.h"

#include <gmp.h>
#include <gmpxx.h>

using namespace smt;
using namespace std;
using namespace wasim;


template <typename T, typename... Rest>
inline void hashCombine(std::size_t &seed, T const &v, Rest &&... rest) {
    std::hash<T> hasher;
    seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    (int[]){0, (hashCombine(seed, std::forward<Rest>(rest)), 0)...};
}

struct NodeData{
    Term term; // will be nullptr if it is for a term with array sort
    uint64_t bit_width;
    std::vector<std::string> simulation_data;

    private:
        NodeData(Term t, uint64_t bw)
            : term(t), bit_width(bw) {}

    public:
        void extend_val(SmtSolver& solver) {
            if (term == nullptr)
                return; // array

            Term value = solver->get_value(term);
            auto valstr = value->to_string();
            if (valstr == "true")
                valstr = "#b1";
            else if (valstr == "false")
                valstr = "#b0";
            // maybe other format conversions?
            simulation_data.push_back(valstr);
        }

        size_t hash() const {
            size_t hash_val = 0;
            for (const auto & v : simulation_data) {
                // hash_val ^= (hash_val << 6) + (hash_val >> 2) + 0x9e3779b9 + std::hash<std::string>{} (v);
                hashCombine(hash_val, v);
            }
            return hash_val;
        }

        bool operator==(const NodeData& other) const {
            if (term == nullptr)
                return false; // for array
            return simulation_data == other.simulation_data;
        }

        static NodeData from_term(const Term& term) {
            SortKind sk = term->get_sort()->get_sort_kind();
            switch (sk) {
                case ARRAY:
                    return NodeData(nullptr, 0);
                case BV:
                    return NodeData(term, term->get_sort()->get_width());
                case BOOL:
                    return NodeData(term, 1);
                default:
                    throw std::invalid_argument("Unsupported sort: " + term->get_sort()->to_string());
            }
        }
        
};

void collect_terms(const Term &term, std::unordered_map<Term, NodeData>& node_data_map ) {
    if (!term) {
        throw std::invalid_argument("Null term provided to collect_terms");
    }

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
        auto res = node_data_map.emplace(current_term, NodeData::from_term(current_term));
        assert (res.second);
        
        for (auto child : current_term) {
            if (child) {  // Ensure child is not null
                node_stack.push(child);
            }
        }
    }
}

void collect_termdata(SmtSolver& solver, std::unordered_map<Term, NodeData>& node_data_map ) {
    for (auto & term_data_pair : node_data_map) {
        term_data_pair.second.extend_val(solver);
    }
}


bool compare_terms(const Term& var1, const Term& var2, SmtSolver& solver) {
    if (!var1 || !var2) {
        return false;
    }
    try {
        TermVec not_equal_term = {solver->make_term(Not, solver->make_term(Equal, var1, var2))};
        auto res = solver->check_sat_assuming(not_equal_term);
        return res.is_unsat();
    } catch (const std::exception& e) {
        std::cerr << "Error comparing terms: " << e.what() << std::endl;
        return false;
    }
}



// RAII wrapper for GMP random state
class GmpRandStateGuard {
    gmp_randstate_t state;

public:
    GmpRandStateGuard() {
        gmp_randinit_default(state);
        gmp_randseed_ui(state, time(NULL));
    }

    ~GmpRandStateGuard() {
        gmp_randclear(state);
    }

    void random_128(mpz_t& rand_num) {
        mpz_init2(rand_num, 128);
        mpz_urandomb(rand_num, state, 128);
    }

    operator gmp_randstate_t&() { return state; }
};


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

    TransitionSystem sts2(solver);
    BTOR2Encoder btor_parser2("../design/idpv-test/aes_case/AES_Verilog.btor2", sts2, "b::");

    auto b_key_term = sts2.lookup("b::key");
    auto b_input_term = sts2.lookup("b::in");
    auto b_output_term = sts2.lookup("b::out");    

    //Assert constraints
    solver->assert_formula( sts1.init() );
    solver->assert_formula( sts2.init() );
    for (const auto & c : sts1.constraints())
        solver->assert_formula(c.first);
    for (const auto & c : sts2.constraints())
        solver->assert_formula(c.first);

    if (!a_key_term || !a_input_term || !b_input_term || !b_key_term || !a_output_term || !b_output_term) {
        throw std::runtime_error("Required terms not found in models");
    }

    auto res_ast = solver->make_term(Equal, a_output_term, b_output_term); // move the outer of the loop

    std::unordered_map<Term, NodeData> node_data_map;
    collect_terms(res_ast, node_data_map);

    // simulation iterations below    
    GmpRandStateGuard rand_guard;

    int num_iterations = 1;
    for (int i = 0; i < num_iterations; ++i) {
        mpz_t key_mpz, input_mpz;
        rand_guard.random_128(key_mpz);
        rand_guard.random_128(input_mpz);

        // Use RAII for GMP strings
        unique_ptr<char, void(*)(void*)> key_str(mpz_get_str(NULL, 10, key_mpz), free);
        unique_ptr<char, void(*)(void*)> input_str(mpz_get_str(NULL, 10, input_mpz), free);

        auto input_val = solver->make_term(key_str.get(), a_key_term->get_sort());
        auto key_val = solver->make_term(input_str.get(), a_input_term->get_sort());

        TermVec assumptions{
            solver->make_term(Equal, a_key_term, key_val),
            solver->make_term(Equal, a_input_term, input_val),
            solver->make_term(Equal, b_key_term, key_val),
            solver->make_term(Equal, b_input_term, input_val)
        };

        auto check_result = solver->check_sat_assuming(assumptions);
        if (!check_result.is_sat()) {
            throw std::runtime_error("Unexpected UNSAT result during simulation");
        }

        collect_termdata(solver, node_data_map);

        mpz_clear(key_mpz);
        mpz_clear(input_mpz);
    } // end of simulation

    cout << "node_data_map size : " << node_data_map.size() << endl;

    solver->assert_formula(solver->make_term(smt::Equal, a_key_term, b_key_term));
    solver->assert_formula(solver->make_term(smt::Equal, a_input_term, b_input_term));

    std::unordered_map<size_t, TermVec> hash_term_map; // the hash of nodeData

    for (const auto& entry : node_data_map) {
        auto entry_first = entry.first;
        const NodeData& node_data = entry.second;
        size_t hash_val = node_data.hash();
        hash_term_map[hash_val].push_back(entry_first);
    }

    cout << "hash_term_map size : " << hash_term_map.size() << endl;

    for (const auto& hash_group : hash_term_map) {
        const auto& terms = hash_group.second;
        if (terms.size() > 1) {
            cout << "terms.size: " << terms.size() << endl;
            for (size_t i = 0; i < terms.size(); ++i) {
                for (size_t j = i + 1; j < terms.size(); ++j) {
                    const auto& term1 = terms[i];
                    const auto& term2 = terms[j];
                    
                    if (term1->get_sort() == term2->get_sort()) {
                        if (compare_terms(term1, term2, solver)) {
                            std::cout << "Equivalent terms found at hash " << hash_group.first << std::endl;
                        }
                    }
                }
            }
        }
    }

    std::unordered_map<Term, int> node_depth_map;



    rand_guard.~GmpRandStateGuard();
    return 0;
}


// if (other_sim_data.hash() == hash_term_pair.first) {
                //     // potentially, check SMT equivalence
                //     auto sort1 = other_sim_data.term->get_sort();
                //     auto sort2 = hash_term_pair.second[0]->get_sort();
                //     cout << sort1 << " " << sort2 << endl;
                //     if(sort1 == sort2){
                //         auto res_eq = compare_terms(other_sim_data.term, hash_term_pair.second[0], solver);
                //         if (res_eq){
                //                 cout << "these two terms are equivalent" << endl;
                //             }
                //         }else{
                //             cout << "no equal nodes" << endl;
                //         }
                // }

//TODO: merge的时候应该先merge靠近input的node，这里需要用一些depth的想法来做。
//然后，hash_term_map中需要 进行判断 TermVec中的Term数量大于等于2 再进行处理，否则跳过
//merge 用 subsitutionwalker 以及visit 来做