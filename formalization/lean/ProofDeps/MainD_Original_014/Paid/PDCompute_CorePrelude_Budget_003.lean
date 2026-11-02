module
public import Paid.PDCompute_CorePrelude_InputNumbers_002
public import Paid.PDROC_EndpointOperands_Budget_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
@[expose] public section

namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDCompute.CoreSearchBudget

/-- Internal certificates computed from ORIGINAL input parameters.
The single global run budget is never passed back into these formulas. -/
def inputBudget (P : Parameters) (fee : ℚ) : ℕ := 256*coreOperandBound P fee
def endpointBudget (P : Parameters) (fee : ℚ) : ℕ :=
  PDROC.EndpointOperands.operandBudget P (inputBudget P fee)
def calibrationBudget (P : Parameters) (fee : ℚ) : ℕ :=
  PDLower.CalibrationCompute.calleeOperandBudget P calibrationEntry (endpointBudget P fee)
    (ratEncodingBits P.certificate.gamma)
def prefixBudget (P : Parameters) (fee : ℚ) : ℕ := 1048576*coreOperandBound P fee

theorem original_Q_covers_rows (P : Parameters) : P.certificate.M+3≤P.certificate.Q := by
  have menu : ((P.certificate.M : ℚ)+1)/P.certificate.gamma≤P.certificate.Q :=
    (Nat.le_ceil _).trans (by exact_mod_cast P.Q_ge_menu_ceil)
  have multiplied:=mul_le_mul_of_nonneg_right P.certificate.gamma_le_quarter
    (by positivity : (0:ℚ)≤(P.certificate.M : ℚ)+3)
  have below : (P.certificate.M : ℚ)+3≤((P.certificate.M : ℚ)+1)/P.certificate.gamma := by
    apply (le_div_iff₀ P.certificate.gamma_pos).mpr
    nlinarith
  have actual:=below.trans menu
  exact_mod_cast actual

/-- Endpoint powers are paid by the ORIGINAL Q*gamma term, rather than
being charged again to a caller state or the output table. -/
theorem endpoint_rational_le_core (P : Parameters) (fee : ℚ) :
    PDROC.EndpointOperands.rationalBudget P≤256*coreOperandBound P fee := by
  have rows:=original_Q_covers_rows P
  have power : PDROC.EndpointOperands.powerBudget P≤
      16*((P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)) := by
    unfold PDROC.EndpointOperands.powerBudget
    calc
      _≤(P.certificate.Q+1)*(16*(ratEncodingBits P.certificate.gamma+2)) :=
        Nat.mul_le_mul (by omega) (by omega)
      _=_ := by ring
  have intrinsic : (P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)≤coreOperandBound P fee := by
    unfold coreOperandBound
    omega
  have gamma : ratEncodingBits P.certificate.gamma≤coreOperandBound P fee := by
    have multiplied:=Nat.mul_le_mul_right (ratEncodingBits P.certificate.gamma+2) (by omega : 1≤P.certificate.Q+1)
    simp only [Nat.one_mul] at multiplied
    omega
  have feeBits : ratEncodingBits P.reviewFee≤coreOperandBound P fee := by unfold coreOperandBound rawSize;omega
  have count : natBits P.certificate.M≤coreOperandBound P fee := by unfold coreOperandBound;omega
  have positive:=coreOperandBound_positive P fee
  unfold PDROC.EndpointOperands.rationalBudget
  omega

/-- One original endpoint call and one original calibration call. These
are closed original-input bounds; they do NOT form B→16B recurrences. -/
theorem prefix_certificate_bounds (P : Parameters) (fee : ℚ) :
    endpointBudget P fee≤16384*coreOperandBound P fee ∧
      calibrationBudget P fee≤524288*coreOperandBound P fee ∧
      calibrationBudget P fee+natBits bodyStart+16≤prefixBudget P fee := by
  have rational:=endpoint_rational_le_core P fee
  have positive:=coreOperandBound_positive P fee
  have endpoint : endpointBudget P fee≤16384*coreOperandBound P fee := by
    unfold endpointBudget inputBudget PDROC.EndpointOperands.operandBudget
    omega
  have intrinsic : (P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)≤coreOperandBound P fee := by
    unfold coreOperandBound
    omega
  have staticOrigin : natBits calibrationEntry=9 := by decide
  have staticEnd : natBits bodyStart≤64 := by rw [initial_body_start_actual];decide
  have calibration : calibrationBudget P fee≤524288*coreOperandBound P fee := by
    have scaled:=Nat.mul_le_mul_left 1024 intrinsic
    unfold calibrationBudget PDLower.CalibrationCompute.calleeOperandBudget
    rw [staticOrigin]
    simp only [Nat.mul_assoc]
    omega
  exact ⟨endpoint,calibration,by unfold prefixBudget;omega⟩

theorem existing_global_budget_suffices (P : Parameters) (fee : ℚ) (pcUpper : ℕ) :
    prefixBudget P fee≤PDCompute.CoreGlobalBudget.budget P fee pcUpper := by
  have original:=PDCompute.CoreGlobalBudget.budget_core P fee pcUpper
  unfold prefixBudget
  omega

end PDCompute.CorePrelude
