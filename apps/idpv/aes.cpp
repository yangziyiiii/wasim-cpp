#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smtlib_reader.h"
#include "smt-switch/utils.h"

#include <random>
#include <cstdlib>
#include <ctime> 
#include <iostream>

using namespace smt;
using namespace std;
using namespace wasim;

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

    std::cout << "a_key:" << a_key_term->to_string() << std::endl;
    std::cout << "a_input:" << a_input_term->to_string() << std::endl;
    std::cout << "a_output:" << a_output_term->to_string() << std::endl;

    TransitionSystem sts2(solver);
    BTOR2Encoder btor_parser2("../design/idpv-test/aes_case/AES_Verilog.btor2", sts2, "b::");

    auto b_key_term = sts2.lookup("b::key");
    auto b_input_term = sts2.lookup("b::in");
    auto b_output_term = sts2.lookup("b::out");    

    std::cout << "b_key:" << b_key_term->to_string() << std::endl;
    std::cout << "b_input:" << b_input_term->to_string() << std::endl;
    std::cout << "b_output:" << b_output_term->to_string() << std::endl;

    solver->assert_formula( sts1.init() );
    solver->assert_formula( sts2.init() );
    for (const auto & c : sts1.constraints())
        solver->assert_formula(c.first);
    for (const auto & c : sts2.constraints())
        solver->assert_formula(c.first);

    solver->assert_formula(solver->make_term(Equal, a_key_term, b_key_term));
    solver->assert_formula(solver->make_term(Equal, a_input_term, b_input_term));
    solver->assert_formula(solver->make_term(Not, solver->make_term(Equal, a_output_term, b_output_term)));

    std::cout << "Checking..." << std::endl;
    auto r = solver->check_sat();
    std::cout << r.to_string() << std::endl;

    return 0;
}

