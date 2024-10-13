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

struct NodeData{
    Term term;
    uint64_t bit_width;
    std::vector<std::string> simulation_data;

    private:
        NodeData(Term t, uint64_t bw, std::vector<std::string>&& sim_data)
            : term(t), bit_width(bw), simulation_data(sim_data) {}

    public:
        NodeData() : term(nullptr), bit_width(0), simulation_data() {}

        bool operator==(const NodeData& other) const {
            return term->hash() == other.term->hash();
        }

        static NodeData get_simulation_data(const Term& term, SmtSolver& solver) {
            SortKind sk = term->get_sort()->get_sort_kind();
            if(sk == ARRAY){
                return NodeData();
            }else if(sk ==BV){
                Term value = solver->get_value(term);
                auto bit_width = value->get_sort()->get_width(); 
                std::vector<std::string> simulation_data;
                simulation_data.push_back(value->to_string());
                return NodeData(term, bit_width, std::move(simulation_data));
            }else{
                cerr << "Unsupported sort: " << sk << std::endl;
                return NodeData();
            }
        }
};

bool compare_terms(const Term& var1, const Term& var2, SmtSolver& solver) {
    TermVec not_equal_term = {solver->make_term(Not, solver->make_term(smt::Equal, var1, var2))};
    auto res = solver->check_sat_assuming(not_equal_term);    
    return res.is_unsat();
}

gmp_randstate_t state;
void random_128(mpz_t& rand_num){
    mpz_init2(rand_num, 128); 
    mpz_urandomb(rand_num, state, 128); 
    // gmp_printf("%032Zx\n", rand_num);
}

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

    Term a_key_ast = nullptr;
    Term a_datain_ast = nullptr;
    Term b_key_ast = nullptr;
    Term b_in_ast = nullptr;


    if (a_key_term != nullptr \
        && a_input_term != nullptr \
        && b_input_term != nullptr \
        && b_key_term != nullptr) 
        {
            a_key_ast = a_key_term;
            a_datain_ast = a_input_term;
            b_in_ast = b_input_term;
            b_key_ast = b_key_term;
        }

    gmp_randinit_default(state);
    gmp_randseed_ui(state, time(NULL)); 

    std::map<std::pair<Term, Term>, int> equivalence_counts;

    int num_iterations = 10;
    for (int i = 0; i < num_iterations; ++i) {
        mpz_t a_key_mpz, a_datain_mpz, b_key_mpz, b_in_mpz; 

        random_128(a_key_mpz);
        random_128(a_datain_mpz);
        random_128(b_key_mpz);
        random_128(b_in_mpz);

        char* a_key_str = mpz_get_str(NULL, 10, a_key_mpz);
        char* a_datain_str = mpz_get_str(NULL, 10, a_datain_mpz);
        char* b_key_str = mpz_get_str(NULL, 10, b_key_mpz);
        char* b_in_str = mpz_get_str(NULL, 10, b_in_mpz);

        auto a_key_assumption = solver->make_term(a_key_str, a_key_ast->get_sort());
        auto a_input_assumption = solver->make_term(a_datain_str, a_datain_ast->get_sort());
        auto b_key_assumption = solver->make_term(b_key_str, b_key_ast->get_sort());
        auto b_input_assumption = solver->make_term(b_in_str, b_in_ast->get_sort());

        Term assumption_equal_a_key = solver->make_term(smt::Equal, a_key_ast, a_key_assumption);
        Term assumption_equal_a_datain = solver->make_term(smt::Equal, a_datain_ast, a_input_assumption); 
        Term assumption_equal_b_in = solver->make_term(smt::Equal, b_in_ast, b_input_assumption); 
        Term assumption_equal_b_key = solver->make_term(smt::Equal, b_key_ast, b_key_assumption); 
       
        
        TermVec assumptions{assumption_equal_a_key, assumption_equal_a_datain, assumption_equal_b_in, assumption_equal_b_key};
        auto sim_data_ast = solver->check_sat_assuming(assumptions);

        auto res_ast = solver->make_term(Equal, a_output_term, b_output_term);

        std::unordered_map<size_t, NodeData> term_hash_map;

        if(sim_data_ast.is_sat()){
            cout << "--------maybe equal-------" << endl;
            std::unordered_set<Term> visited_nodes;
            std::stack<Term> node_stack;
            node_stack.push(res_ast);

            while(!node_stack.empty()){
                Term current_term = node_stack.top();
                node_stack.pop();
                if(visited_nodes.find(current_term) != visited_nodes.end())
                    continue;
                visited_nodes.insert(current_term);

                size_t current_term_hash = current_term->hash();
                cout << "current_term_hash: " << current_term_hash << endl;
                if (term_hash_map.find(current_term_hash) != term_hash_map.end()) {
                    cout << "Term has been seen before, skipping..." << endl;
                    continue;
                }
                
                NodeData data_temp = NodeData::get_simulation_data(current_term, solver);
                auto a = data_temp.term->hash();
                cout << a << endl;


                term_hash_map[current_term_hash] = data_temp;
                // if (data_temp.bit_width > 0) {
                //     for (const auto& data : data_temp.simulation_data) {
                //         std::cout << "data:" << data << " ";
                //     }
                //     std::cout << std::endl;
                // } else {
                //     std::cerr << "Failed to get simulation data." << std::endl;
                // }
            }          
        }


        delete[] a_key_str;
        delete[] a_datain_str;
        delete[] b_key_str;
        delete[] b_in_str;

        mpz_clear(a_key_mpz);
        mpz_clear(a_datain_mpz);
        mpz_clear(b_key_mpz);
        mpz_clear(b_in_mpz);
    }

    // for (const auto& pair_count : equivalence_counts) {
    //     if(pair_count.second == num_iterations){
    //         if(compare_terms(pair_count.first.first, pair_count.first.second, solver)){
    //             equivalence_counts[pair_count.first] = pair_count.second; //这里应该改成一些启发式的方法，不能直接这样merge
    //         }
    //     }
    // }

    // for (const auto& pair : equivalence_counts) {
    //     cout << equivalence_counts.size() << endl;
    // }
    
    gmp_randclear(state);
    return 0;
}