module

public import Paid.PDLower_CalibrationCompute_HeadCorrect_049
public import Paid.RootD27Bits_SlotPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits

namespace PDLower.CalibrationCompute

/-- Numerical cap for the actual natural arithmetic and addresses. Old
scratch values are carried by SafeBits rather than bounded by this cap. -/
def calleeNaturalCap (base endpoints returnPC M Q : ℕ) : ℕ :=
  base+endpoints+returnPC+Q+6*M+64

theorem calleeNaturalCap_bits (P : Parameters) (base endpoints returnPC callerBudget : ℕ) (before : State)
    (arguments : CallArguments P base endpoints returnPC before) (safe : SafeBits before callerBudget) :
    natBits (calleeNaturalCap base endpoints returnPC P.certificate.M P.certificate.Q)≤5*callerBudget+10 := by
  have baseBits := safe.register .fresh
  have endpointBits := safe.register .address
  have returnBits := safe.register .old
  have mBits := safe.register .total
  have qBits := safe.register .index
  rw [arguments.fresh] at baseBits
  rw [arguments.address] at endpointBits
  rw [arguments.old] at returnBits
  rw [arguments.total] at mBits
  rw [arguments.index] at qBits
  change 1+natBits base≤callerBudget at baseBits
  change 1+natBits endpoints≤callerBudget at endpointBits
  change 1+natBits returnPC≤callerBudget at returnBits
  change 1+natBits P.certificate.M≤callerBudget at mBits
  change 1+natBits P.certificate.Q≤callerBudget at qBits
  have first := PDROC.DataBits.natBits_add_le base endpoints
  have second := PDROC.DataBits.natBits_add_le (base+endpoints) returnPC
  have third := PDROC.DataBits.natBits_add_le (base+endpoints+returnPC) P.certificate.Q
  have fourth := PDROC.DataBits.natBits_add_le (base+endpoints+returnPC+P.certificate.Q) (6*P.certificate.M)
  have fifth := PDROC.DataBits.natBits_add_le (base+endpoints+returnPC+P.certificate.Q+6*P.certificate.M) 64
  have multiply := PDROC.DataBits.natBits_mul_le 6 P.certificate.M
  have six : natBits 6=3 := by decide
  have sixtyFour : natBits 64=7 := by decide
  unfold calleeNaturalCap
  omega

theorem calleeNaturalCap_cell (P : Parameters) (base endpoints returnPC callerBudget value : ℕ) (before : State)
    (arguments : CallArguments P base endpoints returnPC before) (safe : SafeBits before callerBudget)
    (bounded : value≤calleeNaturalCap base endpoints returnPC P.certificate.M P.certificate.Q) :
    (.natural value : Cell).bits≤5*callerBudget+11 := by
  have cap := calleeNaturalCap_bits P base endpoints returnPC callerBudget before arguments safe
  have smaller := PDROC.DataBits.natBits_mono bounded
  change 1+natBits value≤5*callerBudget+11
  omega

theorem calleeNaturalCap_workspace (base endpoints returnPC M Q address : ℕ)
    (inside : address∈workspace base M) : address≤calleeNaturalCap base endpoints returnPC M Q := by
  obtain ⟨offset,inside,equal⟩ := Finset.mem_image.mp inside
  have offsetBound : offset<workspaceSize M := Finset.mem_range.mp inside
  rw [workspaceSize_linear] at offsetBound
  unfold calleeNaturalCap
  omega

theorem calleeNaturalCap_endpoint (base endpoints returnPC M Q offset : ℕ)
    (bounded : offset≤rowWidth M+3) : endpoints+offset≤calleeNaturalCap base endpoints returnPC M Q := by
  unfold calleeNaturalCap rowWidth at *
  omega

theorem kernel_pc_encodingBits (origin counter : ℕ)
    (bounded : counter≤origin+(labels.map blockLength).sum+4) : natBits counter≤natBits origin+14 := by
  have length : (labels.map blockLength).sum≤8192 := by decide
  have size : counter≤origin+8196 := by omega
  have smaller := PDROC.DataBits.natBits_mono size
  have added := PDROC.DataBits.natBits_add_le origin 8196
  have constant : natBits 8196=14 := by decide
  omega

end PDLower.CalibrationCompute
