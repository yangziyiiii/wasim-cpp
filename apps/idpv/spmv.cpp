#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smtlib_reader.h"

using namespace wasim;
using namespace smt;

int main() {
    SmtSolver solver = BoolectorSolverFactory::create(false);
    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    // std::cout << "---------------------------Verilog btor---------------------------" << std::endl;
  
    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser("../design/idpv-test/spmv/verilog/spmv.btor2", sts);
    std::cout << "Trans:" << sts.trans()->to_string() << std::endl;

    // SymbolicExecutor executor(sts,solver);
    // assignment_type initdiv = {};
    // auto initial_state = executor.convert(initdiv);
    // executor.init(initial_state);
    // auto initial_input = executor.convert(
    //     {{"clk",1},{"dividend","a"},{"divisor","b"},{"rst",0},{"start",1}});
    // auto v_a = initial_input.at(sts.lookup("dividend"));
    // auto v_b = initial_input.at(sts.lookup("divisor"));


    // std::cout <<"Vlg a expr: " << v_a ->to_string() << std::endl;
    // std::cout <<"Vlg b expr: " << v_b ->to_string() << std::endl;

    // executor.set_input(initial_input,{});
    // executor.sim_one_step();

    // auto s1 = executor.get_curr_state();
    // auto v_ret = s1.get_sv().at(sts.lookup("quotient"));

    // std::vector<decltype(s1)> states;
    // states.push_back(s1);
    // // auto done_o  = s1.get_sv().at(sts.lookup("done_o"));


    // for(int i = 0; i < 65; i++){
    //     executor.set_input(executor.convert({{"clk",1},{"start",0},{"rst",0}}),{});
    //     executor.sim_one_step();

    //     s1 = executor.get_curr_state();
    //     states.push_back(s1);

    //     v_ret   = s1.get_sv().at(sts.lookup("quotient"));
    // }

    // for (const auto & a: s1.get_assumptions() ) {
    //     std::cout << "assumption: " << a->to_string() << std::endl;  // HZ: this is the initial constraint
    //     solver->assert_formula(a);
    // }
    
    std::cout << "---------------------------C++ smtlib2---------------------------" << std::endl;

    smt::SmtLibReader smtlib_reader(solver);
    smtlib_reader.parse("../design/idpv-test/spmv/spmv.smt2");

    // auto c_a = smtlib_reader.lookup_symbol("main::1::dividend!0@1#1");
    // auto c_b = smtlib_reader.lookup_symbol("main::1::divisor!0@1#1");
    // auto c_ret = smtlib_reader.lookup_symbol("main::1::quotient!0@1#7");

    // std::cout << "C a:    " << c_a->to_string() << std::endl;
    // std::cout << "C b:    " << c_b->to_string() << std::endl;
    // std::cout << "C expr: " << c_ret->to_string() << std::endl;

    std::cout << "------------------------equvi check------------------------------" << std::endl;

    // auto v_a_extend = solver->make_term(smt::Op(smt::Zero_Extend,16),v_a);
    // auto check_a = solver->make_term(smt::Equal, v_a, c_a);
    // solver->assert_formula(check_a);
    // auto r = solver->check_sat();
    // if(r.is_sat()){
    //     std::cout<<"a equal"<<std::endl;
    // }

    // auto check_b = solver->make_term(smt::Equal, v_b, c_b);
    // solver->assert_formula(check_b);
    // auto r1 = solver->check_sat();
    // if(r1.is_sat()){
    //     std::cout<<"b equal"<<std::endl;
    // }

    // auto bvsort8 = solver->make_sort(smt::SortKind::BV, 32);
    // auto divisor_not_eq_0 = solver->make_term(smt::Not,
    //     solver->make_term(smt::Equal, v_b, solver->make_term(0, bvsort8)));
    // solver->assert_formula(divisor_not_eq_0);
    // auto r2 = solver->check_sat();
    // if(r2.is_unsat()){
    //     std::cout<<"divisor is 0"<<std::endl;
    // }

    // auto done_expr = solver->make_term(1, solver->make_sort(smt::BV,1));
    // auto check_done_o = solver->make_term(smt::Equal, done_o, done_expr);
    // solver->assert_formula(check_done_o);
    // auto done_o_res = solver->check_sat();
    // if(done_o_res.is_sat()){
    //     std::cout << "done_o is 1" << std::endl;
    // }else if(done_o_res.is_unsat() || done_o_res.is_unknown()){
    //     std::cout << "done_o is not 1" << std::endl;
    // }
    
    // auto check_ret = solver->make_term(smt::Equal, v_ret, c_ret);
    // Term not_equal = solver -> make_term(Not, check_ret);
    // TermVec assumptions{not_equal};
    // auto res_ret = solver->check_sat_assuming(assumptions);
    // if(res_ret.is_unsat()){
    //     std::cout << "always equal" << std::endl;
        
    // } else if(res_ret.is_sat()){
    //     std::cout<<"va:   "<<solver->get_value(v_a)<<std::endl;
    //     std::cout<<"vb:   "<<solver->get_value(v_b)<<std::endl;
    //     std::cout<<"vexpr:"<<solver->get_value(v_ret)<<std::endl;
    //     std::cout<<"ca:   "<<solver->get_value(c_a)<<std::endl;
    //     std::cout<<"cb:   "<<solver->get_value(c_b)<<std::endl;
    //     std::cout<<"cexpr:"<<solver->get_value(c_ret)<<std::endl;
        
    //     std::cout << "exist unequal" << std::endl;

    //     std::ofstream fout("cex.txt");
    //     for (size_t i = 0; i<states.size(); ++i) {
    //         for(const auto & sv_val_pair : states[i].get_sv()) {
    //             fout << sv_val_pair.first->to_string() << " = ";
    //             fout << solver->get_value(sv_val_pair.second)->to_string() << " , ";
    //         }
    //         fout << "\n";
    //     }   

    // }
    return 0;
}