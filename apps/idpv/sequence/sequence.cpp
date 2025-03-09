#include "../sweeping/sweeping.h"

#define SWEEPING_UTILS_H

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <BTOR2_FILE_PATH_1> <BTOR2_FILE_PATH_2> <BOUND> <SIMULATION_ITERATIONS> [SOLVER_TIMEOUT_MS] [PROPERTY_CHECK_TIMEOUT_MS] [DUMP_SMT]" << std::endl;
        std::cerr << "  BTOR2_FILE_PATH: Path to the BTOR2 file" << std::endl;
        std::cerr << "  SIMULATION_ITERATIONS: Number of simulation iterations" << std::endl;
        std::cerr << "  SOLVER_TIMEOUT_MS: Optional timeout for solver in milliseconds (default: 500000)" << std::endl;
        std::cerr << "  PROPERTY_CHECK_TIMEOUT_MS: Optional timeout for property checking in milliseconds (default: 5000000)" << std::endl;
        std::cerr << "  DUMP_SMT: Optional flag to enable/disable SMT dumping (0=disable, 1=enable, default: 1)" << std::endl;
        return 1;
    }

    std::string btor2_file_1 = argv[1];
    std::string btor2_file_2 = argv[2];
    unsigned bound = atoi(argv[3]);

    int num_iterations = 0;
    try {
        num_iterations = std::stoi(argv[4]);
    } catch (const std::invalid_argument& e) {
        std::cerr << "Error: Invalid number format for NUM_ITERATIONS" << std::endl;
        return 1;
    } catch (const std::out_of_range& e) {
        std::cerr << "Error: NUM_ITERATIONS is out of range" << std::endl;
        return 1;
    }

    auto program_start_time = std::chrono::high_resolution_clock::now();
    last_time_point = program_start_time;

    SmtSolver solver = BitwuzlaSolverFactory::create(true);

    // Add timeout parameter, default is 5 seconds
    int solver_timeout_ms = 500000;
    int property_check_timeout_ms = 1000000;
    bool dump_smt = false; // Default is to dump SMT

    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");
    solver->set_opt("time-limit", std::to_string(property_check_timeout_ms / 1000.0));  // set time limit

    // Loading and parsing BTOR2 files
    TransitionSystem sts1(solver);
    BTOR2Encoder btor_parser1(btor2_file_1, sts1, "a::");

    auto datain = sts1.lookup("a::datain");
    auto a_key = sts1.lookup("a::key");
    auto root_a = sts1.lookup("a::finalout");

    TransitionSystem sts2(solver);
    BTOR2Encoder btor_parser2(btor2_file_2, sts2, "b::");

    // auto b_key = sts2.lookup("b::key");
    // auto state = sts2.lookup("b::state");
    // auto root_b = sts2.lookup("b::out");

    auto b_key = sts2.lookup("b::key");
    auto state = sts2.lookup("b::plain_text");
    auto root_b = sts2.lookup("b::cipher_text");

    SymbolicSimulator sim(sts2, solver);


    std::unordered_map<Term, NodeData> node_data_map; // term -> sim_data
    std::unordered_map<uint32_t, TermVec> hash_term_map; // hash -> TermVec
    std::unordered_map<Term, Term> substitution_map; // term -> term, for substitution
    std::unordered_map<Term, std::unordered_map<std::string, std::string>> all_luts; // state -> lookup table

    // const auto & propvec = sts2.prop();
    // if (propvec.empty()) {
    //   std::cout << "No property to check!" << std::endl;
    //   return 1;
    // }
    // auto prop = and_vec(propvec, solver);
    sim.init();

    // if (!check_prop(sim.interpret_state_expr_on_curr_frame(aes_out, false),
    //                 sim.all_assumptions(),
    //                 solver)) {
    //   std::cout << "[bmc] failed at init!" << std::endl;
    //   return 2;
    // }



    

    for (unsigned i = 1; i <= bound; ++i) {
      sim.set_input({}, {});
      sim.sim_one_step();
      smt::UnorderedTermSet out;
      auto bb = sim.interpret_state_expr_on_curr_frame(root_b, false);
      smt::get_free_symbols(root_b, out);
      simulation(out, num_iterations, node_data_map);
    }

    
    

    auto root = solver->make_term(Equal, root_a, root_b);

    std::cout << "============================" << std::endl;

      // cout << "Loading and parsing BTOR2 files..." << endl;

    // const auto & input_terms_1 = btor_parser1.inputsvec();  // all input here
    // const auto & input_terms_2 = btor_parser2.inputsvec();  // all input here
    // const auto & output_terms = btor_parser.get_output_terms();  // all output here
    // const auto & constraints_1 = btor_parser1.get_const_terms();  // all constraints here
    // const auto & constraints_2 = btor_parser2.get_const_terms();  // all constraints here
    const auto & property_1 = btor_parser1.propvec();  // all properties here
    const auto & property_2 = btor_parser2.propvec();  // all properties here
   

    std::cout << "stage 1 : init array & simualtion ...";

    //Array init
    initialize_arrays(sts1, sts2, all_luts, substitution_map);
    //End of array init


    TermVec input_terms;
    input_terms.push_back(datain);
    input_terms.push_back(a_key);
    input_terms.push_back(state);
    input_terms.push_back(b_key);
    //simulation
    simulation(input_terms, num_iterations, node_data_map);

    std::cout << "done" <<std::endl;


    //end of simulation



    
    //start post order traversal
    int count = 0;
    int unsat_count = 0;
    int sat_count = 0;
    int i = 0;
    
    // Check if there's a third command line argument for solver timeout setting
    // if (argc >= 6) {
    //     try {
    //         solver_timeout_ms = std::stoi(argv[5]);
    //     } catch (const std::invalid_argument& e) {
    //         std::cerr << "Warning: Invalid solver timeout value, using default (5000ms)" << std::endl;
    //     } catch (const std::out_of_range& e) {
    //         std::cerr << "Warning: Solver timeout value out of range, using default (5000ms)" << std::endl;
    //     }
    // }
    
    // // Check if there's a fourth command line argument for property check timeout setting
    // if (argc >= 7) {
    //     try {
    //         property_check_timeout_ms = std::stoi(argv[6]);
    //     } catch (const std::invalid_argument& e) {
    //         std::cerr << "Warning: Invalid property check timeout value, using default (5000ms)" << std::endl;
    //     } catch (const std::out_of_range& e) {
    //         std::cerr << "Warning: Property check timeout value out of range, using default (5000ms)" << std::endl;
    //     }
    // }
    
    // // Check if there's a fifth command line argument for SMT dumping option
    // if (argc >= 8) {
    //     try {
    //         int dump_smt_int = std::stoi(argv[7]);
    //         dump_smt = (dump_smt_int != 0);
    //     } catch (const std::invalid_argument& e) {
    //         std::cerr << "Warning: Invalid DUMP_SMT value, using default (enabled)" << std::endl;
    //     } catch (const std::out_of_range& e) {
    //         std::cerr << "Warning: DUMP_SMT value out of range, using default (enabled)" << std::endl;
    //     }
    // }
    
    // std::cout << "Using solver timeout: " << solver_timeout_ms << "ms (" << (solver_timeout_ms / 1000.0) << "s)" << std::endl;
    // std::cout << "Using property check timeout: " << property_check_timeout_ms << "ms (" << (property_check_timeout_ms / 1000.0) << "s)" << std::endl;
    // std::cout << "SMT dumping: " << (dump_smt ? "enabled" : "disabled") << std::endl;

    // std::cout << "stage 2 : begin sweeping ... " << std::endl;
    // std::cout << "============================" << std::endl;

    //Add constraint into root

    // pre_collect_constants(TermVec({root}), node_data_map, hash_term_map, substitution_map, num_iterations);
    // cout << root->to_string() << endl;
    // post_order(root, node_data_map, hash_term_map, substitution_map, all_luts, count, unsat_count, sat_count, solver,num_iterations, solver_timeout_ms);
    // root = substitution_map.at(root);
    // print_time();
    std::cout << "Start checking sat" << std::endl;
    auto not_root = solver->make_term(Not, root);
    solver->assert_formula(not_root);
    std::cout << "Property check timeout set to: " << property_check_timeout_ms << "ms (" << (property_check_timeout_ms / 1000.0)<< "s)" << std::endl;
    
    // Continue with the original solver for checking satisfiability
    auto start_time = std::chrono::high_resolution_clock::now();
    auto res = solver->check_sat();
    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();
    
    // print_time();
    if(res.is_unsat()){
        std::cout << "Result : UNSAT (took " << duration << "ms)" << std::endl;
    } else if(res.is_sat()) {
        std::cout << "Result : SAT (took " << duration << "ms)" << std::endl;
    } else {
        std::cout << "Result : UNKNOWN - likely timed out after " << duration << "ms" << std::endl;
    }
    // cout << "count: " << count << endl;
    // cout << "unsat_count: " << unsat_count << endl;
    // cout << "sat_count: " << sat_count << endl;
    std::cout << "for this property, " << unsat_count << " UNSAT when merging, and " << sat_count << " SAT when merging" <<std::endl;
    cout << "-----------------" << endl;

    // print_time();
    // std::cout << "Start checking sat" << std::endl;
    // std::cout << "All property done" << std:: endl;

    auto program_end_time = std::chrono::high_resolution_clock::now();
    auto total_time = std::chrono::duration_cast<std::chrono::milliseconds>(program_end_time - program_start_time).count();
    std::cout << "Total execution time: " << total_time / 1000.0 << " s" << std::endl;
    std::cout << "============================" << std::endl;

    return 0;
    }
