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

  std::cout << "---------------------------Verilog btor---------------------------" << std::endl;
  
  TransitionSystem sts(solver);
  BTOR2Encoder btor_parser("../design/idpv-test/guangyu_case/top.btor2", sts);
  std::cout << sts.trans()->to_string() << std::endl;
  auto v_a = sts.lookup("A");
  auto v_b = sts.lookup("B");
  auto v_m = sts.lookup("M");
  auto v_n = sts.lookup("N");
  auto v_o = sts.lookup("result");
  auto v_o_next = sts.state_updates().at(v_o);
  std::cout << v_o_next->to_string() << std::endl;

  smt::SmtLibReader smtlib_reader(solver);
  smtlib_reader.parse("../design/idpv-test/guangyu_case/top.smt2");

  auto c_a = smtlib_reader.lookup_symbol("main::1::A!0@1#2");
  auto c_b = smtlib_reader.lookup_symbol("main::1::B!0@1#2");
  auto c_m = smtlib_reader.lookup_symbol("main::1::M!0@1#2");
  auto c_n = smtlib_reader.lookup_symbol("main::1::N!0@1#2");
  auto c_o = smtlib_reader.lookup_symbol("main::1::O!0@1#3");
  std::cout << c_o -> to_string() << std::endl;



  auto c_m_4 = solver-> make_term(smt::Op(smt::PrimOp::Extract,3,0),c_m);
  auto c_n_4 = solver-> make_term(smt::Op(smt::PrimOp::Extract,3,0),c_n);



  auto check_a = solver->make_term(smt::Equal, v_a, c_a);
  auto check_b = solver->make_term(smt::Equal, v_b, c_b);
  auto check_m = solver->make_term(smt::Equal, v_m, c_m_4);
  auto check_n = solver->make_term(smt::Equal, v_n, c_n_4);

  solver->assert_formula(check_a);
  solver->assert_formula(check_b);
  solver->assert_formula(check_m);
  solver->assert_formula(check_n);

  std::cout<< v_o_next->get_sort()<<std::endl;
  std::cout<< c_o->get_sort()<<std::endl;

  auto c_o_63 = solver-> make_term(smt::Op(smt::PrimOp::Extract,62,0),c_o);

  auto check_ret = solver->make_term(smt::Equal, v_o_next, c_o_63);
  Term not_equal = solver -> make_term(Not, check_ret);
  TermVec assumptions{ not_equal};
  auto res_ret = solver->check_sat_assuming(assumptions);
  if(res_ret.is_unsat()){
    std::cout << "always equal" << std::endl;
    
  } else if(res_ret.is_sat()){
    std::cout << "exist unequal" << std::endl;
  }
  
  
  return 0;
}