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
    uint32_t bit_width;
    std::vector<std::string> simulation_data;

    private:
        NodeData(Term t, uint32_t bw, std::vector<std::string>&& sim_data)
            : term(t), bit_width(bw), simulation_data(sim_data) {}

    public:
        NodeData() : term(nullptr), bit_width(0), simulation_data() {}

        bool operator==(const NodeData& other) const {
            return simulation_data == other.simulation_data;
        }

    static NodeData get_simulation_data(const Term& term, SmtSolver& solver) {
        Term value = solver->get_value(term);
        uint32_t bit_width = value->get_sort()->get_width();
        std::vector<std::string> simulation_data;
        simulation_data.push_back(value->to_string());

        return NodeData(term, bit_width, std::move(simulation_data));
    }
};


void traverse_and_collect_terms(const Term &term, SmtSolver& solver, std::unordered_map<Term, NodeData>& node_data_map) {
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



void process_terms(const unordered_map<string, vector<Term>>& value_term_map, SmtSolver& solver) {
    std::unordered_map<Term, Term> term_map;
    for (const auto& entry : value_term_map) {
        const vector<Term>& term_list = entry.second;

        for (const auto& term : term_list) {
            auto it = term_map.find(term);
            if (it != term_map.end()) {
                continue;
            }

            for (const auto& other_term : term_list) {
                if (term != other_term && compare_terms(term, other_term, solver)) {
                    term_map[other_term] = term; // merge into one term
                    cout << "Merge term: " << other_term->to_string() << " with existing term: " << term->to_string() << endl;
                    break;
                }
            }

        }
    }
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

    solver->assert_formula( sts1.init() );

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

    // for (const auto& term : free_symbols_a){ // loop once for all invar
    //     std::string term_str = term->to_string();
    //     if (term_str == sts1.lookup("a::key")->to_string()){
    //         key_ast = term; // key_ast should be a::key
    //         cout << key_ast->to_string() << endl;
    //     }else if(term_str == sts1.lookup("a::datain")->to_string()){
    //         datain_ast = term;
    //         cout << datain_ast->to_string() << endl;
    //     }
    // }

    srand(static_cast<unsigned int>(time(0)));
    int num_iterations = 10; 

    for (int i = 0; i < num_iterations; ++i) {
        int64_t a_key = rand() % 100 + 1;
        int64_t a_datain = rand() % 100 + 1;

        auto key_assumption = solver->make_term(a_key, key_ast->get_sort());
        auto datain_assumption = solver->make_term(a_datain, datain_ast->get_sort());

        Term assumption_equal_a_key = solver->make_term(smt::Equal, key_ast, key_assumption);
        Term assumption_equal_a_datain = solver->make_term(smt::Equal, datain_ast, datain_assumption); 
        TermVec assumptions{assumption_equal_a_key, assumption_equal_a_datain};
        // auto sim_data_ast = solver->check_sat_assuming(assumptions);


    }



    // std::unordered_map<Term, NodeData> node_data_map;
    // traverse_and_collect_terms(sts.trans(), solver, node_data_map);
    // for (const auto& [term, data] : node_data_map) {
    //     cout << "Term: " << term->to_string() <<endl;
    //     cout << "Bit Width: " << data.bit_width <<endl;
    //     cout << "Simulation Data: ";
    //     for (const auto& str : data.simulation_data) {
    //         cout << str << endl;
    //     }
    //     cout << "-----------------------------------------" << endl;
    // }


    //compare simulation data equal or not
    // std::unordered_map<std::string, std::vector<Term>> value_term_map;
    // for (const auto&  [term, data] : node_data_map) {
    //     Term value = solver->get_value(term);
    //     std::string value_term = value->to_string(); // value 对应的 term
    //     value_term_map[value_term].push_back(term);
    // }

    // process_terms(value_term_map,solver);
    
    return 0;
}