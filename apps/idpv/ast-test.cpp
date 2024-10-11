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

using namespace smt;
using namespace std;
using namespace wasim;

struct NodeData{

};

size_t hash_term(const Term& term) {
    cout << term->to_string() << endl;
    return std::hash<string>()(term->to_string());
}

bool compare_terms(const Term& var1, const Term& var2, SmtSolver& solver) {
    TermVec not_equal_term = {solver->make_term(Not, solver->make_term(smt::Equal, var1, var2))};
    auto res = solver->check_sat_assuming(not_equal_term);    
    return res.is_unsat();
}

gmp_randstate_t state;
int random_128(){
    mpz_t rand_num;
    mpz_init2(rand_num, 128); 
    mpz_urandomb(rand_num, state, 128); 
    gmp_printf("%032Zx\n", rand_num);
    return 0;
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

    smt::UnorderedTermSet free_symbols_a;
    get_free_symbols(sts1.trans() , free_symbols_a);
    cout << free_symbols_a.size()<< endl; // compare before & after sweeping

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
        && b_key_term != nullptr) {
            a_key_ast = a_key_term;
            a_datain_ast = a_input_term;
            b_key_ast = b_input_term;
            b_key_ast = b_key_term;
        }

    gmp_randinit_default(state);
    gmp_randseed_ui(state, time(NULL)); 

    std::map<std::pair<Term, Term>, int> equivalence_counts;
    auto res_ast = solver->make_term(Equal, a_output_term, b_output_term);

    int num_iterations = 1;
    for (int i = 0; i < num_iterations; ++i) {
        auto a_key = random_128();
        auto a_datain = random_128();
        auto b_key = random_128();
        auto b_in = random_128();

        auto key_assumption = solver->make_term(a_key, a_key_ast->get_sort());
        auto datain_assumption = solver->make_term(a_datain, a_datain_ast->get_sort());
        // auto 

        Term assumption_equal_a_key = solver->make_term(smt::Equal, a_key_ast, key_assumption);
        Term assumption_equal_a_datain = solver->make_term(smt::Equal, a_datain_ast, datain_assumption); 
        TermVec assumptions{assumption_equal_a_key, assumption_equal_a_datain};
        auto sim_data_ast = solver->check_sat_assuming(assumptions);

        if(sim_data_ast.is_sat()){
            cout << "sim_data_ast.is_sat()" << endl;
            std::unordered_set<Term> visited_nodes;
            std::stack<Term> node_stack;
            node_stack.push(res_ast);

            std::unordered_map<size_t, Term> term_map; 

            while(!node_stack.empty()){
                Term current_term = node_stack.top();
                node_stack.pop();
                if(visited_nodes.find(current_term) != visited_nodes.end())
                    continue;
                visited_nodes.insert(current_term);

                size_t term_hash =hash_term(current_term);

                if(term_map.find(term_hash) != term_map.end()){
                    Term existing_term = term_map[term_hash];
                    if (hash_term(current_term) == hash_term(existing_term)) {
                        cout << "find two nodes maybe equal" << endl;
                        equivalence_counts[{current_term, existing_term}]++;
                    }
                }else{
                    term_map[term_hash] = current_term;
                }
            }
        }
    }

    for (const auto& pair_count : equivalence_counts) {
        if(pair_count.second == num_iterations){
            if(compare_terms(pair_count.first.first, pair_count.first.second, solver)){
                equivalence_counts[pair_count.first] = pair_count.second; //这里应该改成一些启发式的方法，不能直接这样merge
            }
        }
    }

    for (const auto& pair : equivalence_counts) {
        cout << equivalence_counts.size() << endl;
    }
    
    return 0;
}