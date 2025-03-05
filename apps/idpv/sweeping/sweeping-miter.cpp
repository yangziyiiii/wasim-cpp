#include "./sweeping.h"

#define SWEEPING_UTILS_H

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <BTOR2_FILE_PATH> <SIMULATION_ITERATIONS> [SOLVER_TIMEOUT_MS] [PROPERTY_CHECK_TIMEOUT_MS] [DUMP_SMT]" << std::endl;
        std::cerr << "  BTOR2_FILE_PATH: Path to the BTOR2 file" << std::endl;
        std::cerr << "  SIMULATION_ITERATIONS: Number of simulation iterations" << std::endl;
        std::cerr << "  SOLVER_TIMEOUT_MS: Optional timeout for solver in milliseconds (default: 500000)" << std::endl;
        std::cerr << "  PROPERTY_CHECK_TIMEOUT_MS: Optional timeout for property checking in milliseconds (default: 5000000)" << std::endl;
        std::cerr << "  DUMP_SMT: Optional flag to enable/disable SMT dumping (0=disable, 1=enable, default: 1)" << std::endl;
        return 1;
    }

    std::string btor2_file = argv[1];
    
    int num_iterations = 0;
    try {
        num_iterations = std::stoi(argv[2]);
    } catch (const std::invalid_argument& e) {
        std::cerr << "Error: Invalid number format for NUM_ITERATIONS" << std::endl;
        return 1;
    } catch (const std::out_of_range& e) {
        std::cerr << "Error: NUM_ITERATIONS is out of range" << std::endl;
        return 1;
    }

    auto program_start_time = std::chrono::high_resolution_clock::now();
    last_time_point = program_start_time;

    SmtSolver solver = BitwuzlaSolverFactory::create(false);

    // Add timeout parameter, default is 5 seconds
    int solver_timeout_ms = 5000000;
    int property_check_timeout_ms = 100000;
    bool dump_smt = false; // Default is to dump SMT

    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");
    solver->set_opt("time-limit", std::to_string(property_check_timeout_ms / 1000.0));  // set time limit

    // Loading and parsing BTOR2 files
    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser(btor2_file, sts, "a::");

    std::cout << "============================" << std::endl;

    // cout << "Loading and parsing BTOR2 files..." << endl;

    const auto& input_terms = btor_parser.inputsvec(); // all input here
    const auto& output_terms = btor_parser.get_output_terms(); // all output here
    const auto& constraints = btor_parser.get_const_terms(); // all constraints here
    const auto& property = btor_parser.propvec(); // all properties here
    const auto& idvec = btor_parser.idvec();

    // cout << "Constraints: " << constraints.size() << endl;
    for(auto c : constraints) {
        solver->assert_formula(c);
    }

    std::unordered_map<Term, NodeData> node_data_map; // term -> sim_data
    std::unordered_map<uint32_t, TermVec> hash_term_map; // hash -> TermVec
    std::unordered_map<Term, Term> substitution_map; // term -> term, for substitution
    std::unordered_map<Term, std::unordered_map<std::string, std::string>> all_luts; // state -> lookup table

     std::cout << "stage 1 : init array & simualtion ...";

    //Array init
    initialize_arrays(sts, all_luts, substitution_map);
    //End of array init

    //simulation
    simulation(input_terms, num_iterations, sts, node_data_map);
    std::cout << "done" <<std::endl;
   

    for(auto i : input_terms){
        assert(node_data_map[i].get_simulation_data().size() == num_iterations);
        substitution_map.insert({i, i});
        hash_term_map[node_data_map[i].hash()].push_back(i);
    }
    //end of simulation

    solver->assert_formula(sts.init());
    for (const auto & c : sts.constraints()) solver->assert_formula(c.first);
    
    //start post order traversal
    int count = 0;
    int unsat_count = 0;
    int sat_count = 0;
    int i = 0;
    
    // Check if there's a third command line argument for solver timeout setting
    if (argc >= 4) {
        try {
            solver_timeout_ms = std::stoi(argv[3]);
        } catch (const std::invalid_argument& e) {
            std::cerr << "Warning: Invalid solver timeout value, using default (5000ms)" << std::endl;
        } catch (const std::out_of_range& e) {
            std::cerr << "Warning: Solver timeout value out of range, using default (5000ms)" << std::endl;
        }
    }
    
    // Check if there's a fourth command line argument for property check timeout setting
    if (argc >= 5) {
        try {
            property_check_timeout_ms = std::stoi(argv[4]);
        } catch (const std::invalid_argument& e) {
            std::cerr << "Warning: Invalid property check timeout value, using default (5000ms)" << std::endl;
        } catch (const std::out_of_range& e) {
            std::cerr << "Warning: Property check timeout value out of range, using default (5000ms)" << std::endl;
        }
    }
    
    // Check if there's a fifth command line argument for SMT dumping option
    if (argc >= 6) {
        try {
            int dump_smt_int = std::stoi(argv[5]);
            dump_smt = (dump_smt_int != 0);
        } catch (const std::invalid_argument& e) {
            std::cerr << "Warning: Invalid DUMP_SMT value, using default (enabled)" << std::endl;
        } catch (const std::out_of_range& e) {
            std::cerr << "Warning: DUMP_SMT value out of range, using default (enabled)" << std::endl;
        }
    }
    
    std::cout << "Using solver timeout: " << solver_timeout_ms << "ms (" << (solver_timeout_ms / 1000.0) << "s)" << std::endl;
    std::cout << "Using property check timeout: " << property_check_timeout_ms << "ms (" << (property_check_timeout_ms / 1000.0) << "s)" << std::endl;
    std::cout << "SMT dumping: " << (dump_smt ? "enabled" : "disabled") << std::endl;

    std::cout << "stage 2 : begin sweeping ... " << std::endl;
    std::cout << "============================" << std::endl;

    //Add constraint into root
    std::vector<Term> traversal_roots; 
    traversal_roots.push_back(sts.init());
    for(auto constraint_pair : sts.constraints()) {
        traversal_roots.push_back(constraint_pair.first);
    }
    // for(auto it : input_terms) {
    //     traversal_roots.push_back(it);
    // }

    // cout << "Prop: " << property.size() << endl;
    for(auto root : property) {
        
        traversal_roots.push_back(root);
        pre_collect_constants(traversal_roots, node_data_map, hash_term_map, substitution_map, num_iterations);
        std::set<Term> unique_roots(traversal_roots.begin(), traversal_roots.end());
        std::vector<Term> final_roots(unique_roots.begin(), unique_roots.end());

        // for(auto t : final_roots) {
        //     std::cout << "***: " << t->to_string() << std::endl;
        //     std::cout << "sort: "<< t->get_sort() << std::endl;
        // }

        // cout << final_roots.size() << endl;
        // if(final_roots.empty()){
        //     std::cerr << "Error: final_roots is empty!" << std::endl;
        //     exit(1);
        // }
        // else if(final_roots.size() == 1){
        //     Term combined_term = final_roots[0];
        // } else {
        //     Term combined_term = solver->make_term(And, final_roots);
        // }
        Term combined_term = solver->make_term(And, final_roots);


        // cout << root->to_string() << endl;
        post_order(combined_term, node_data_map, hash_term_map, substitution_map, all_luts, count, unsat_count, sat_count, solver, num_iterations, solver_timeout_ms);
        root = substitution_map.at(root);

        // std::cout << "Sweeping done, begin the last solving using bitwuzla for this preperty" << std::endl;
        cout << "Property ID: " << idvec[i] << " ";
        // print_time();
        // std::cout << "Start checking sat" << std::endl;
        solver->push();
        auto not_root = solver->make_term(Not, root);
        solver->assert_formula(not_root);
        
        if (dump_smt) {
            // Create a new solver instance for dumping SMT files
            SmtSolver dump_solver = BitwuzlaSolverFactory::create(false);
            dump_solver->set_logic("QF_UFBV");
            
            // Use TermTranslator to transfer terms to the new solver
            smt::TermTranslator translator(dump_solver);
            auto translated_not_root = translator.transfer_term(not_root);
            dump_solver->assert_formula(translated_not_root);
            
            // Dump SMT files using the new solver instance
            // dump_solver->dump_smt2("property_" + std::to_string(idvec[i]) + ".smt2");
            std::string safe_path = btor2_file;
            std::replace(safe_path.begin(), safe_path.end(), '/', '_');
            std::replace(safe_path.begin(), safe_path.end(), '\\', '_');
            dump_solver->dump_smt2("property_" + std::to_string(idvec[i]) + "_" + safe_path + ".smt2");
            std::cout << "SMT file dumped for property " << idvec[i] << std::endl;
        }
        
        // Set the property check timeout
        
        std::cout << "Property check timeout set to: " << property_check_timeout_ms << "ms (" << (property_check_timeout_ms / 1000.0) << "s)" << std::endl;
        
        // Continue with the original solver for checking satisfiability
        auto start_time = std::chrono::high_resolution_clock::now();
        auto res = solver->check_sat();
        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();
        
        solver->pop();
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
        std::cout << "for this property, " << unsat_count << " UNSAT when merging, and " << sat_count << " SAT when merging" << std::endl;
        cout << "-----------------" << endl;

        i++;
    }
    // print_time();
    // std::cout << "Start checking sat" << std::endl;
    std::cout << "All property done" << std:: endl;

    auto program_end_time = std::chrono::high_resolution_clock::now();
    auto total_time = std::chrono::duration_cast<std::chrono::milliseconds>(program_end_time - program_start_time).count();
    std::cout << "Total execution time: " << total_time / 1000.0 << " s" << std::endl;
    std::cout << "============================" << std::endl;

    return 0;
}
