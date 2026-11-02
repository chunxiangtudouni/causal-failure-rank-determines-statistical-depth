module

public import Paid.PDLower_CalibrationCompute_CallerBitBudget_087
public import Paid.PDLower_CalibrationCompute_PostRowScalarBits_085

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits

namespace PDLower.CalibrationCompute

/-- The complete old caller budget is carried with a constant factor;
new rational values use the shared LINEAR-Q scale. No parameter-only
bound is imposed on old scratch or on old live workspace cells. -/
def calleeOperandBudget (P : Parameters) (origin callerBudget Lgamma : ℕ) : ℕ :=
  16*callerBudget+1024*(P.certificate.Q+1)*(Lgamma+2)+natBits origin+64

theorem calleeOperandBudget_initial (P : Parameters) (origin callerBudget Lgamma : ℕ) (before : State)
    (safe : SafeBits before callerBudget) : SafeBits before (calleeOperandBudget P origin callerBudget Lgamma) := by
  intro bits member
  have old := safe bits member
  unfold calleeOperandBudget
  omega

theorem calleeOperandBudget_natural (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma value : ℕ)
    (before : State) (arguments : CallArguments P base endpoints returnPC before) (safe : SafeBits before callerBudget)
    (bounded : value≤calleeNaturalCap base endpoints returnPC P.certificate.M P.certificate.Q) :
    (Cell.natural value).bits≤calleeOperandBudget P origin callerBudget Lgamma := by
  have old := calleeNaturalCap_cell P base endpoints returnPC callerBudget value before arguments safe bounded
  unfold calleeOperandBudget
  omega

theorem calleeOperandBudget_rational (P : Parameters) (origin callerBudget Lgamma : ℕ) (value : ℚ)
    (bounded : ratEncodingBits value≤128*(P.certificate.Q+1)*(Lgamma+2)) :
    (Cell.rational value).bits≤calleeOperandBudget P origin callerBudget Lgamma := by
  change 1+ratEncodingBits value≤_
  unfold calleeOperandBudget
  simp only [Nat.mul_assoc] at bounded ⊢
  omega

theorem labelAddress_upper (origin : ℕ) (label : Label) : labelAddress origin label≤origin+(labels.map blockLength).sum := by
  have split := congrArg (fun pieces : List Label => (pieces.map blockLength).sum)
    (List.take_append_drop (labels.idxOf label) labels)
  simp only [List.map_append,List.sum_append] at split
  unfold labelAddress
  omega

theorem calleeOperandBudget_pc (P : Parameters) (origin callerBudget Lgamma : ℕ) (label : Label) (count : ℕ)
    (bounded : count≤32) : natBits (labelAddress origin label+count)≤calleeOperandBudget P origin callerBudget Lgamma := by
  have start := labelAddress_upper origin label
  have shifted := kernel_pc_encodingBits (origin+32) (labelAddress origin label+count) (by omega)
  have added := PDROC.DataBits.natBits_add_le origin 32
  have constant : natBits 32=6 := by decide
  unfold calleeOperandBudget
  omega

theorem basicBlock_length_le_32 (label : Label) : (basicBlock label).body.length≤32 := by
  cases label <;> decide

end PDLower.CalibrationCompute
