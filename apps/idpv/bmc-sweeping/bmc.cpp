#include "../sweeping/sweeping.h"

int main(int argc, char* argv[]) {
    if (argc < 4) {
        std::cout << "[Usage] " << argv[0] << " btor bound " << "sim iteration" << std::endl;
        return 1;
    }

    std::string btor2_file = argv[1];
    unsigned bound = atoi(argv[2]);
    int num_iterations = std::stoi(argv[3]);
  
    auto program_start_time = std::chrono::high_resolution_clock::now();
    last_time_point = program_start_time;
    SmtSolver solver = BitwuzlaSolverFactory::create(false);

    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    // Loading and parsing BTOR2 files
    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser(btor2_file, sts);

    // cout << "Loading and parsing BTOR2 files..." << endl;

    const auto& input_terms = btor_parser.inputsvec(); // all input here
    const auto& output_terms = btor_parser.get_output_terms(); // all output here
    const auto& constraints = btor_parser.get_const_terms(); // all constraints here
    const auto& property = btor_parser.propvec(); // all properties here
    const auto& idvec = btor_parser.idvec();

    SymbolicSimulator sim(sts, solver);
    const auto & propvec = sts.prop();
    if (propvec.empty()) {
        std::cout << "No property to check!" << std::endl;
        return 1;
    }
    auto prop = and_vec(propvec, solver);
    sim.init();

    if (! check_prop(
        sim.interpret_state_expr_on_curr_frame(prop, false),
        sim.all_assumptions(),
        solver )) {
        std::cout << "[bmc] failed at init!" << std::endl;
        return 2;
    }

    for (unsigned i = 1; i<=bound; ++i) {

        //init for each bound
        std::unordered_map<Term, NodeData> node_data_map; // term -> sim_data
        std::unordered_map<uint32_t, TermVec> hash_term_map; // hash -> TermVec
        std::unordered_map<Term, Term> substitution_map; // term -> term, for substitution
        std::unordered_map<Term, std::unordered_map<std::string, std::string>> all_luts; // state -> lookup table
        auto root = sim.interpret_state_expr_on_curr_frame(prop, false);

        initialize_arrays(sts, all_luts, substitution_map);
        simulation(input_terms, num_iterations, node_data_map);
        for(auto i : input_terms){
            assert(node_data_map[i].get_simulation_data().size() == num_iterations);
            substitution_map.insert({i, i});
            hash_term_map[node_data_map[i].hash()].push_back(i);
        }
        smt::UnorderedTermSet out;
        smt::get_free_symbols(root,out);
        simulation(out, num_iterations, node_data_map);
        int count = 0;
        int unsat_count = 0;
        int sat_count = 0;
        //end of init

        sim.set_input({},{});
        sim.sim_one_step();

        post_order(root, node_data_map, hash_term_map, substitution_map, all_luts, count, unsat_count, sat_count, solver, num_iterations);
        root = substitution_map.at(root);

        if (check_prop(
          root,
          sim.all_assumptions(),
          solver )) {
            print_time();
            std::cout << "[bmc] bound " << i << " passed." << std::endl;
            cout << "total: " << count << " ,unsat:  " << unsat_count << " ,sat: " << sat_count << endl;
        } else {
            print_time();
            std::cout << "[bmc] failed at bound " << i << std::endl;
            cout << "total: " << count << " ,unsat:  " << unsat_count << " ,sat: " << sat_count << endl;
          return 2;
        }

        node_data_map.clear();
        substitution_map.clear();
        hash_term_map.clear();
    }

    auto program_end_time = std::chrono::high_resolution_clock::now();
    auto total_time = std::chrono::duration_cast<std::chrono::milliseconds>(program_end_time - program_start_time).count();
    std::cout << "Total execution time: " << total_time / 1000.0 << " s" << std::endl;

    return 0;
}