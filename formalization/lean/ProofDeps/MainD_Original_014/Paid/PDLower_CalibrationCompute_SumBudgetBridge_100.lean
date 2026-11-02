module

public import Paid.PDLower_CalibrationCompute_RowBitBudget_102
public import Paid.PDLower_CalibrationCompute_SumLoopBits_098

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

/-- Discharge EVERY intrinsic summation operand inequality from the
original caller, actual two-row pointers and the common denominator/mass
theorem. There is no external accumulator or whole-prefix bound premise. -/
theorem calleeOperandBudget_sum (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma level read write : ℕ)
    (before : State) (arguments : CallArguments P base endpoints returnPC before) (safe : SafeBits before callerBudget)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma)
    (buffers : PDROC.CalibrationRow.Buffers base P.certificate.M read write) (levelBound : level≤P.certificate.M+1) :
    SumOperandBounds origin base read level (calleeOperandBudget P origin callerBudget Lgamma)
      (P.walkRow level true P.certificate.Q) := by
  have control := calleeOperandBudget_control P origin base endpoints returnPC callerBudget Lgamma before arguments safe
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro offset member
    have bounded : offset≤16 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    exact ControlBudget.slot P origin base _ offset control bounded
  · intro cursor inside
    have bound : cursor≤rowWidth P.certificate.M := by unfold rowWidth; omega
    exact (ControlBudget.rowAddress P origin base _ read write cursor control buffers bound).1
  · intro cursor inside
    have bounded : cursor+1≤controlNaturalCap P base := by
      have lower := (controlNaturalCap_lower P base).2.1
      unfold rowWidth at lower
      omega
    exact ControlBudget.nat P origin base _ (cursor+1) control bounded
  · intro count bounded
    have actual := walkRowPrefix_encodingBits P Lgamma level P.certificate.Q count gammaBits (by omega)
    have coefficient := Nat.mul_le_mul_right (Lgamma+2)
      (Nat.mul_le_mul_right (P.certificate.Q+1) (by decide : 5≤128))
    exact calleeOperandBudget_rational P origin callerBudget Lgamma _ (actual.trans coefficient)
  · exact ControlBudget.literal P origin base _ 0 control (by decide)
  · exact ControlBudget.literal P origin base _ 1 control (by decide)
  · intro label count bounded
    exact calleeOperandBudget_pc P origin callerBudget Lgamma label count (bounded.trans (basicBlock_length_le_32 label))

end PDLower.CalibrationCompute
