module

public import Paid.PDROC_D27Prepare_Search_005
public import Paid.PDROC_D27Prepare_Memory_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid
open PaperProofs.Paid.Computation

namespace PDROC.D27Prepare.Search

open Program Memory

def majoritySetupMemory (D : CertificateInput) (memory : SlotMemory) : SlotMemory :=
  (((((((((memory.write 22 (.rational D.stages)).write 24 (.rational (D.gamma ^ 2))).write 32
    (.rational (4 * D.gamma ^ 2))).write 25 (.rational D.varianceBase)).write 26
    (.rational (D.varianceBase ^ 2))).write 32 (.rational (2 * (D.stages : ℚ)))).write 33
    (.rational (D.risk / (2 * (D.stages : ℚ))))).write 27
    (.rational ((D.risk / (2 * (D.stages : ℚ))) ^ 2))).write 28 (.rational D.varianceBase))

/-- The page1 command specification evaluates from original scalar cells;
the search powers and threshold are computed rather than supplied. -/
theorem majoritySetup_eval (D : CertificateInput) (memory : SlotMemory)
    (stages : Has memory 0 (.natural D.stages))
    (gamma : Has memory 2 (.rational D.gamma))
    (risk : Has memory 3 (.rational D.risk))
    (one : Has memory 17 (.rational 1))
    (two : Has memory 18 (.rational 2))
    (four : Has memory 20 (.rational 4)) :
    slotSequenceEval majoritySetupCommands memory = some (majoritySetupMemory D memory) := by
  have hN : (D.stages : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt D.stages_pos)
  have denominator : (2 : ℚ) * D.stages ≠ 0 := mul_ne_zero (by norm_num) hN
  simp [majoritySetupCommands, slotSequenceEval, SlotCommand.eval, majoritySetupMemory,
    SlotMemory.write, Cell.nat?, Cell.rat?, RatOp.eval,
    stages.1, stages.2, gamma.1, gamma.2, risk.1, risk.2,
    one.1, one.2, two.1, two.2, four.1, four.2, denominator,
    CertificateInput.varianceBase, pow_two]

end PDROC.D27Prepare.Search
