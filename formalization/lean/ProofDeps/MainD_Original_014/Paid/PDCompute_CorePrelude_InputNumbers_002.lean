module
public import Paid.PDCompute_CorePrelude_Layout_001
public import Paid.PDCompute_CoreGlobalBudget_Polynomial_005
public import Paid.PDLower_CalibrationCompute_StandaloneResources_129
public import PaperProofs.Paid.PDROC_DataBits_Counts_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
@[expose] public section

namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDCompute.CoreSearchBudget PDCompute.CoreGlobalBudget

/-- The original calibration intrinsic scale is already in the original
core envelope; no fee-sign or extra input qualification is needed. -/
theorem calibration_scale_le_core (P : Parameters) (fee : ℚ) :
    PDLower.CalibrationCompute.calibrationBitScale P fee≤coreOperandBound P fee := by
  have factor : 1≤(P.certificate.stages+1)*(2*(P.certificate.M+1)+2) := by
    exact (Nat.mul_le_mul (by omega : 1≤P.certificate.stages+1) (by omega : 1≤2*(P.certificate.M+1)+2))
  have menu:=Nat.mul_le_mul_right (maximumMenuBits P fee+1) factor
  simp only [Nat.one_mul] at menu
  unfold PDLower.CalibrationCompute.calibrationBitScale coreOperandBound
  omega

/-- Original Q already pays ceil(gamma inverse), so the actual old
certificate bit-size can be compared without a polynomial-size oracle. -/
theorem certificate_size_le_core (P : Parameters) (fee : ℚ) :
    dataInputSize P.certificate≤coreOperandBound P fee := by
  have menu : ((P.certificate.M : ℚ)+1)/P.certificate.gamma≤P.certificate.Q :=
    (Nat.le_ceil _).trans (by exact_mod_cast P.Q_ge_menu_ceil)
  have inverse : P.certificate.gamma⁻¹≤((P.certificate.M : ℚ)+1)/P.certificate.gamma := by
    rw [←one_div]
    apply div_le_div_of_nonneg_right _ P.certificate.gamma_pos.le
    have nonneg : (0 : ℚ) ≤ P.certificate.M := Nat.cast_nonneg _
    linarith
  have ceilBound : ⌈P.certificate.gamma⁻¹⌉₊≤P.certificate.Q := Nat.ceil_le.mpr (inverse.trans menu)
  have intrinsic:=Nat.mul_le_mul_right (ratEncodingBits P.certificate.gamma+2)
    (by omega : 1≤P.certificate.Q+1)
  simp only [Nat.one_mul] at intrinsic
  have qgamma : P.certificate.Q+ratEncodingBits P.certificate.gamma+1≤
      (P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2) := by
    nlinarith [Nat.zero_le (P.certificate.Q*ratEncodingBits P.certificate.gamma)]
  unfold dataInputSize coreOperandBound rawSize
  omega

/-- Use the already proved original count polynomial only to bound the
LOGARITHMIC representation of t0/M/E/Q. The resulting bit bound is linear
in the original core envelope, rather than a quartic preparation budget. -/
theorem prepared_count_cell_bits (P : Parameters) (fee : ℚ) (value : ℕ)
    (bounded : value≤P.certificate.t0+P.certificate.M+P.certificate.E+P.certificate.Q) :
    (Cell.natural value).bits≤64*coreOperandBound P fee := by
  have count:=certificate_counts_bound P.certificate
  have monotone:=natBits_mono (bounded.trans count)
  have product:=natBits_mul_le 128 ((dataInputSize P.certificate)^8)
  have power:=natBits_pow_le (dataInputSize P.certificate) 8
  have number : natBits 128=8 := by decide
  have logarithm:=natBits_le_succ (dataInputSize P.certificate)
  have source:=certificate_size_le_core P fee
  have positive:=coreOperandBound_positive P fee
  change 1+natBits value≤_
  omega

/-- ALL thirteen actual readonly core input cells, including the derived
certificate counters, Lambda and zero-charge risk. No endpoint/calibration
cache, heap, trace, fee positivity or scalar metadata is provided. -/
theorem prepared_input_cell_bits (P : Parameters) (fee : ℚ) (cell : Cell)
    (member : cell∈preparedInput P fee) : cell.bits≤64*coreOperandBound P fee := by
  have positive:=coreOperandBound_positive P fee
  have dimensions : P.certificate.stages+natBits P.tools+ratEncodingBits P.certificate.risk+
      ratEncodingBits P.reviewFee+ratEncodingBits fee+1≤coreOperandBound P fee := by
    unfold coreOperandBound rawSize
    omega
  have intrinsic:=Nat.mul_le_mul_right (ratEncodingBits P.certificate.gamma+2)
    (by omega : 1≤P.certificate.Q+1)
  simp only [Nat.one_mul] at intrinsic
  have gamma : ratEncodingBits P.certificate.gamma≤coreOperandBound P fee := by
    unfold coreOperandBound
    omega
  have Jfactor:=Nat.mul_le_mul_left (P.bisectionBudget fee+1)
    (by omega : 1≤ratEncodingBits P.Lambda+ratEncodingBits P.certificate.risk+1)
  simp only [Nat.mul_one] at Jfactor
  have J : P.bisectionBudget fee+1≤coreOperandBound P fee := by
    unfold coreOperandBound
    omega
  have lambda:=(PDCompute.CoreGlobalBudget.original_initial_prices P fee).2
  have zeroRisk:=zeroChargeRisk_encoding P fee
  simp only [preparedInput,List.mem_append] at member
  rcases member with raw|derived
  · simp only [rawInput,List.mem_cons,List.not_mem_nil,or_false] at raw
    rcases raw with rfl|rfl|rfl|rfl|rfl|rfl
    · have bits:=natBits_le_succ P.certificate.stages
      change 1+natBits P.certificate.stages≤_
      omega
    · change 1+natBits P.tools≤_
      omega
    · change 1+ratEncodingBits P.certificate.gamma≤_
      omega
    · change 1+ratEncodingBits P.certificate.risk≤_
      omega
    · change 1+ratEncodingBits P.reviewFee≤_
      omega
    · change 1+ratEncodingBits fee≤_
      omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at derived
    rcases derived with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact prepared_count_cell_bits P fee _ (by omega)
    · exact prepared_count_cell_bits P fee _ (by omega)
    · exact prepared_count_cell_bits P fee _ (by omega)
    · exact prepared_count_cell_bits P fee _ (by omega)
    · have bits:=natBits_le_succ (P.bisectionBudget fee)
      change 1+natBits (P.bisectionBudget fee)≤_
      omega
    · change 1+ratEncodingBits P.Lambda≤_
      omega
    · change 1+ratEncodingBits (P.zeroChargeRisk fee)≤_
      omega

end PDCompute.CorePrelude
