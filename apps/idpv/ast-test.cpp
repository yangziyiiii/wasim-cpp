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
    uint64_t bit_width;
    std::vector<std::string> simulation_data;

    private:
        NodeData(Term t, uint64_t bw, std::vector<std::string>&& sim_data)
            : term(t), bit_width(bw), simulation_data(sim_data) {}

    public:
        NodeData() : term(nullptr), bit_width(0), simulation_data() {}

        bool operator==(const NodeData& other) const {
            return simulation_data == other.simulation_data;
        }

    static NodeData get_simulation_data(const Term& term, SmtSolver& solver) {
        SortKind sk = term->get_sort()->get_sort_kind();
        if(sk == ARRAY){
            cout << "array" << endl;
            return NodeData();
        }else if(sk ==BV){
            cout << "BV" << endl;
            Term value = solver->get_value(term);
            auto bit_width = value->get_sort()->get_width(); 
            std::vector<std::string> simulation_data;
            simulation_data.push_back(value->to_string());

            return NodeData(term, bit_width, std::move(simulation_data));
        }else{
            cerr << "other sort" << endl;
        }
        
    }
};

void collect_TermData(const Term &term, SmtSolver& solver, std::unordered_map<Term, NodeData>& node_data_map) {
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

bool compare_terms(const Term& var1, const Term& var2, SmtSolver& solver) {
    TermVec not_equal_term = {solver->make_term(Not, solver->make_term(smt::Equal, var1, var2))};
    auto res = solver->check_sat_assuming(not_equal_term);    
    return res.is_unsat();
}

std::unordered_map<Term, Term> parent_map;
int get_depth(const Term& term, const Term& root) {
    int depth = 0;
    Term current = term;
    while (current != root && parent_map.count(current)) {
        current = parent_map.at(current);
        depth++;
    }
    return (current == root) ? depth : -1;
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
    cout << "a_key:" << a_key_term->to_string() << endl;

    smt::UnorderedTermSet free_symbols_a;
    get_free_symbols(sts1.trans() , free_symbols_a);
    cout << free_symbols_a.size()<< endl; // compare before & after sweeping


    Term key_ast = nullptr;
    Term datain_ast = nullptr;

    if (a_key_term != nullptr) {
        key_ast = a_key_term;
        cout << key_ast->to_string() << endl;
    }

    if (a_input_term != nullptr) {
        datain_ast = a_input_term;
        cout << datain_ast->to_string() << endl;
    }

    srand(static_cast<unsigned int>(time(0)));
    int num_iterations = 10; 

    std::map<std::pair<Term, Term>, int> equivalence_counts;

    for (int i = 0; i < num_iterations; ++i) {
        int64_t a_key = rand() % 100 + 1;
        int64_t a_datain = rand() % 100 + 1;

        auto key_assumption = solver->make_term(a_key, key_ast->get_sort());
        auto datain_assumption = solver->make_term(a_datain, datain_ast->get_sort());

        Term assumption_equal_a_key = solver->make_term(smt::Equal, key_ast, key_assumption);
        Term assumption_equal_a_datain = solver->make_term(smt::Equal, datain_ast, datain_assumption); 
        TermVec assumptions{assumption_equal_a_key, assumption_equal_a_datain};
        auto sim_data_ast = solver->check_sat_assuming(assumptions);

        if(sim_data_ast.is_sat()){
            std::unordered_map<Term, NodeData> node_data_map;
            collect_TermData(sts1.trans(),solver,node_data_map);
            
            for (const auto& entry1 : node_data_map) {
                for (const auto& entry2 : node_data_map) {
                    cout << entry1.first->get_sort()->to_string() << endl;
                    cout << entry2.first->get_sort()->to_string() << endl;

                    if (entry1.first != entry2.first \
                        && entry1.first->get_sort()->to_string() == entry2.first->get_sort()->to_string() \
                        && compare_terms(entry1.first, entry2.first, solver)) {
                         equivalence_counts[{entry1.first, entry2.first}]++;
                    }
                }
            }

            std::unordered_map<Term, Term> term_merge_map;
            for (const auto& pair_count : equivalence_counts) {
                if (pair_count.second == num_iterations) {
                    Term term1 = pair_count.first.first;
                    Term term2 = pair_count.first.second;

                    int depth1 = get_depth(term1, sts1.trans());
                    int depth2 = get_depth(term2, sts1.trans());

                    if (depth1 >=0 && depth2 >= 0 ) {
                    if (depth1 < depth2) {
                        term_merge_map[term2] = term1;
                    } else {
                        term_merge_map[term1] = term2;
                    }
                    cout << "Merging: " << (depth1 < depth2 ? term2 : term1)->to_string() 
                        << " into " << (depth1 < depth2 ? term1 : term2)->to_string() << endl;
                    }

                }
            }

        }
    }
    
    return 0;
}