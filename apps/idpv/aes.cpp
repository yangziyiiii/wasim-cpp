#include <chrono>
#include "assert.h"
#include "config/testpath.h"
#include "frontend/btor2_encoder.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smtlib_reader.h"

using namespace smt;
using namespace std;
using namespace wasim;


int main() {
    SmtSolver solver = BoolectorSolverFactory::create(false);
    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser1("../design/idpv-test/aes_case/aes_all/aes_all_one_round.btor2", sts);
    cout << "-------" << endl;
    BTOR2Encoder btor_parser2("../design/idpv-test/aes_case/AES-Verilog/AES_Verilog_one_round.btor2", sts);

    cout << sts.trans()->to_string() << endl;

    

    


    return 0;
}
