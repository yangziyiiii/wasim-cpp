/**
 * This is to put conditional equvialence to s-expression/json
 * 
*/

/*

Dividend: R0
Divider:  D
Output Q,R

Expression: D*Q+R - R0


you don't need to have the C++ part

(cond ...)
(expr ...)


*/

#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smtlib_reader.h"
#include "smt-switch/cvc5_factory.h"
#include "smt-switch/printing_solver.h"

#include "framework/egraph/json_export.h"

using namespace wasim;
using namespace smt;

void export_smt(const std::string & fname,
        const Term & v, const Term & quotient, const Term & remainder, const Term & divisor, const Term & dividend) {
    std::ofstream fout(fname);
    if(!fout.is_open())
        return;
    auto cvc5solver = Cvc5SolverFactory::create(false);
    auto printer = cvc5solver;
    TermTranslator translater(cvc5solver);

    auto v_trans = translater.transfer_term(v);
    auto quotient_trans = translater.transfer_term(quotient);
    auto remainder_trans = translater.transfer_term(remainder);
    auto divisor_trans = translater.transfer_term(divisor);
    auto dividend_trans = translater.transfer_term(dividend);

    // printer->assert_formula(v_trans);
    fout << "(declare-fun " << dividend->to_string() << " () " << dividend->get_sort()->to_string()  << ")" << std::endl;
    fout << "(declare-fun " << divisor->to_string() << " () " << divisor->get_sort()->to_string()  << ")" << std::endl;

    fout << "(" << "assert" << " " << v_trans->to_string() << ")" << std::endl;
    // v_valid |=> ( v_quotient * v_b + v_remainder - v_a ) == 0
    auto final_width = dividend_trans->get_sort()->get_width();

    auto q = quotient_trans;
    auto d = divisor_trans;
    auto r = remainder_trans;

    auto s1 = printer->make_term(BVMul, q, d);
    //std::cout << "s1 width=" << s1->get_sort()->get_width() << "\n";
    auto s2 = printer->make_term(BVAdd, s1, r);
    //std::cout << "r width=" << r->get_sort()->get_width() << "\n";
    //std::cout << "s2 width=" << s2->get_sort()->get_width() << "\n";
    auto s3 = printer->make_term(BVSub, s2, dividend_trans);

            
    auto zero = printer->make_term(0, printer->make_sort(BV, final_width));
    
    auto check = printer->make_term(Not,
            printer->make_term(Equal, s3, zero));

    fout << "(" << "assert" << " " << check->to_string() << ")" << std::endl;
    fout << "(check-sat)" << std::endl;
}


int main() {    
    using std::chrono::high_resolution_clock;
    using std::chrono::duration_cast;
    using std::chrono::duration;
    using std::chrono::milliseconds;

    SmtSolver solver = BoolectorSolverFactory::create(false);
    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    // std::cout << "---------------------------Verilog btor---------------------------" << std::endl;
  
    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser("../design/idpv-test/div_case/suoglu_div.btor2", sts);
    std::cout << "Trans:" << sts.trans()->to_string() << std::endl;

    SymbolicExecutor executor(sts,solver);
    assignment_type initdiv = {};
    auto initial_state = executor.convert(initdiv);
    executor.init(initial_state);
    auto initial_input = executor.convert(
        {{"clk",1},{"dividend","a"},{"divisor","b"},{"rst",0},{"start",1}});
    auto v_a = initial_input.at(sts.lookup("dividend"));
    auto v_b = initial_input.at(sts.lookup("divisor"));


    std::cout <<"Vlg a expr: " << v_a ->to_string() << std::endl;
    std::cout <<"Vlg b expr: " << v_b ->to_string() << std::endl;

    executor.set_input(initial_input,{});
    executor.sim_one_step();

    auto s1 = executor.get_curr_state();
    auto v_ret = s1.get_sv().at(sts.lookup("quotient"));

    std::vector<decltype(s1)> states;
    states.push_back(s1);

    for(int i = 0; i < 65; i++){
        auto iv_map = executor.convert({{"clk",1},{"start",0},{"rst",0}});
        executor.set_input(iv_map,{});
        executor.sim_one_step();

        s1 = executor.get_curr_state();
        states.push_back(s1);
    }

    for (const auto & a: s1.get_assumptions() ) {
         // HZ: this is the initial constraint
        solver->assert_formula(a);
    }

    std::cout << "------------------------equvi check------------------------------" << std::endl;

    auto bvsort8 = solver->make_sort(smt::SortKind::BV, 32);
    auto divisor_not_eq_0 = solver->make_term(smt::Not,
        solver->make_term(smt::Equal, v_b, solver->make_term(0, bvsort8)));
    solver->assert_formula(divisor_not_eq_0);

    auto r2 = solver->check_sat();
    assert(r2.is_sat()); // Sanity check to ensure the existing constraints are satisfiable
    // before actually applying the unequal check

    for (int i=0; i<states.size(); ++i) {

        std::cout << "Cycle:"<<i+1;
        std::cout.flush();
        

        const auto & s = states.at(i);
        auto v_quotient = s.get_sv().at(sts.lookup("quotient"));
        auto v_remainder = s.get_sv().at(sts.lookup("remainder"));


        auto iv_map = executor.convert({{"clk",1},{"start",0},{"rst",0}});
        auto v_valid = s.interpret_expr_on_curr_state_and_input(sts.lookup("valid"), solver, iv_map);

        auto sat_result1 = solver->check_sat_assuming({v_valid});
        if (!sat_result1.is_sat()) {
            std::cout << " (skipped)\n";
            continue;
        }

        //std::ofstream f_valid("../design/idpv-test/div_case/egraph-export/valid_"+std::to_string(i+1));
        //f_valid << smt_layered_printing(v_valid);
        smt_to_json(v_valid, "../design/idpv-test/div_case/egraph-export/valid_"+std::to_string(i+1)+".json");

        //std::ofstream f_quotient("../design/idpv-test/div_case/egraph-export/quotient_"+std::to_string(i+1));
        //f_quotient << smt_layered_printing(v_quotient);
        smt_to_json(v_quotient, "../design/idpv-test/div_case/egraph-export/quotient_"+std::to_string(i+1)+".json");

        //std::ofstream f_remainder("../design/idpv-test/div_case/egraph-export/remainder_"+std::to_string(i+1));
        //f_remainder << smt_layered_printing(v_remainder);
        smt_to_json(v_remainder, "../design/idpv-test/div_case/egraph-export/remainder_"+std::to_string(i+1)+".json");
        
        std::cout << " (json exported)";
        std::cout.flush();

        export_smt("../design/idpv-test/div_case/egraph-export/smt_"+std::to_string(i+1)+".smt2",
            v_valid, v_quotient, v_remainder,  v_b, v_a  );

        std::cout << " (smt2 exported)\n";

        // v_valid |=> ( v_quotient * v_b + v_remainder - v_a ) == 0

        // if (i == 10)
        //    break;


    }

    return 0;
}