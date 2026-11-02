module

public import Paid.PDLower_CalibrationCompute_CalleeBitEnvelope_099
public import Paid.PDROC_CalibrationRow_ControlOperands_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

/-- Static numerical bounds come from the real original entry, once.
All later rows retain this fixed budget rather than expanding it again. -/
theorem calleeOperandBudget_control (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma : ℕ)
    (before : State) (arguments : CallArguments P base endpoints returnPC before) (safe : SafeBits before callerBudget) :
    ControlBudget P origin base (calleeOperandBudget P origin callerBudget Lgamma) := by
  refine ⟨?_,?_,?_⟩
  · unfold calleeOperandBudget
    omega
  · have bounded : controlNaturalCap P base≤calleeNaturalCap base endpoints returnPC P.certificate.M P.certificate.Q := by
      unfold controlNaturalCap firstRow rowWidth calleeNaturalCap
      omega
    exact calleeOperandBudget_natural P origin base endpoints returnPC callerBudget Lgamma (controlNaturalCap P base)
      before arguments safe bounded
  · intro label
    exact calleeOperandBudget_pc P origin callerBudget Lgamma label 32 (le_refl _)

theorem calleeOperandBudget_row (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma : ℕ)
    (before : State) (arguments : CallArguments P base endpoints returnPC before) (safe : SafeBits before callerBudget)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) :
    RowBudget P origin base Lgamma (calleeOperandBudget P origin callerBudget Lgamma) := by
  refine ⟨calleeOperandBudget_control P origin base endpoints returnPC callerBudget Lgamma before arguments safe,gammaBits,?_⟩
  unfold calleeOperandBudget
  simp only [Nat.mul_assoc]
  omega

end PDLower.CalibrationCompute
