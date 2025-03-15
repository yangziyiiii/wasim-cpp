#include "../sweeping/sweeping.h"

int main(int argc, char* argv[]) {
    Config config;

    if (!parse_arguments(argc, argv, config)) {
        return EXIT_FAILURE;
    }

    // DEBUG
    if (config.debug) {
        std::cout << "==== DEBUG ====" << std::endl;
        std::cout << "BTOR2 File           : " << config.btor2_file << std::endl;
        std::cout << "Simulation Iterations: " << config.simulation_iterations << std::endl;
        std::cout << "Solver Timeout (ms)  : " << config.solver_timeout_ms << std::endl;
        std::cout << "Property Timeout (ms): " << config.property_check_timeout_ms << std::endl;
        std::cout << "Dump SMT Enabled     : " << (config.dump_smt ? "Yes" : "No") << std::endl;
        std::cout << "Debug Enabled        : " << (config.debug ? "Yes" : "No") << std::endl;
        std::cout << "===============" << std::endl;
    }

    //parameter
    std::string btor2_file = config.btor2_file;
    int num_iterations = config.simulation_iterations;
    bool dump_smt = config.dump_smt;
    int solver_timeout_ms = config.solver_timeout_ms;
    int property_check_timeout_ms = config.property_check_timeout_ms;
    bool debug = config.debug;
    int bound = config.bound;
    std::string dump_input_file = config.dump_input_file;
    std::string load_input_file = config.load_input_file;

    //logging solver
    auto program_start_time = std::chrono::high_resolution_clock::now();
    last_time_point = program_start_time;
    SmtSolver solver = BitwuzlaSolverFactory::create(false);

    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    // Loading and parsing BTOR2 files
    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser(btor2_file, sts, "a::");

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

        //FIXME dump smt2 file for bitwuzla
        // sim.set_input({}, {});
        // sim.sim_one_step();
        // smt::TermVec prop_at_curr_frame = sim.interpret_state_expr_on_curr_frame(propvec, false);
        // smt::Term not_property = solver->make_term(Not, and_vec(prop_at_curr_frame, solver));
        // solver->assert_formula(not_property);
        // for(auto a : sim.all_assumptions()) {
        //     solver->assert_formula(a);
        // }
        // solver->dump_smt2("property_" + std::to_string(i) + ".smt2");

       

        sim.set_input({},{});
        sim.sim_one_step();

        //check property
        auto done_signal = sts.lookup("a::all_done");
        smt::Term done_term = sim.interpret_state_expr_on_curr_frame(done_signal, false);
        smt::Term done_check = solver->make_term(Equal, done_term, solver->make_term(1, done_term->get_sort()));

        solver->push();
        for (auto a : sim.all_assumptions()) {
            solver->assert_formula(a);
        }
        solver->assert_formula(done_check);

        Result r = solver->check_sat();

        if(r.is_sat()) {

            // init for each bound
            std::unordered_map<Term, NodeData> node_data_map; // term -> sim_data
            std::unordered_map<uint32_t, TermVec> hash_term_map; // hash -> TermVec
            std::unordered_map<Term, Term> substitution_map; // term -> term, for substitution
            std::unordered_map<Term, std::unordered_map<std::string, std::string>> all_luts; // state -> lookup table
            smt::TermVec prop_at_curr_frame = sim.interpret_state_expr_on_curr_frame(propvec, false);
            auto root = and_vec(prop_at_curr_frame, solver);

            initialize_arrays({&sts}, all_luts, substitution_map, debug);
            simulation(input_terms, num_iterations, node_data_map, solver, dump_input_file, load_input_file, constraints);
            for(auto i : input_terms){
                assert(node_data_map[i].get_simulation_data().size() == num_iterations);
                substitution_map.insert({i, i});
                hash_term_map[node_data_map[i].hash()].push_back(i);
            }
            smt::UnorderedTermSet out;
            smt::get_free_symbols(root,out);
            simulation(out, num_iterations, node_data_map, solver, dump_input_file, load_input_file, constraints);
            int count = 0;
            int unsat_count = 0;
            int sat_count = 0;

            
            //end of init
            
            post_order(root, node_data_map, hash_term_map, substitution_map, all_luts, count, unsat_count, sat_count, solver, num_iterations,dump_smt, input_terms, property_check_timeout_ms, debug, dump_input_file, load_input_file);
            print_time();
            // root = substitution_map.at(root);
            std::cout<<std::endl;
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
        solver->pop();
    }

    auto program_end_time = std::chrono::high_resolution_clock::now();
    auto total_time = std::chrono::duration_cast<std::chrono::milliseconds>(program_end_time - program_start_time).count();
    std::cout << "Total execution time: " << total_time / 1000.0 << " s" << std::endl;

    return 0;
}