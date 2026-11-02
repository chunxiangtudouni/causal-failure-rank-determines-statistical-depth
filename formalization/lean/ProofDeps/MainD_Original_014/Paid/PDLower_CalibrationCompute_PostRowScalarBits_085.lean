module

public import Paid.PDLower_CalibrationCompute_SumBits_059
public import Paid.PDLower_CalibrationCompute_CalibrationValue_039

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDLower.CalibrationCompute

theorem half_sub_scalar_encodingBits (value : ℚ) (budget : ℕ)
    (bounded : ratEncodingBits value≤budget) :
    ratEncodingBits (1/2-value)≤2*budget+8 := by
  have half : ratEncodingBits (1/2 : ℚ)=4 := by
    norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have subtract := PDROC.DataBits.ratEncodingBits_sub_le (1/2 : ℚ) value
  rw [half] at subtract
  omega

/-- The genuine total-rational weight, including the zero branch, uses
only a constant number of arithmetic operations. No unit-mass or
normalization hypothesis is imposed on this ratio. -/
theorem computedWeight_scalar_encodingBits (error q : ℚ) (errorBudget qBudget : ℕ)
    (errorBits : ratEncodingBits error≤errorBudget) (qBits : ratEncodingBits q≤qBudget) :
    ratEncodingBits (computedWeight error q)≤2*(errorBudget+qBudget)+16 := by
  have numerator := half_sub_scalar_encodingBits error errorBudget errorBits
  have denominator := half_sub_scalar_encodingBits q qBudget qBits
  have divide := PDROC.DataBits.ratEncodingBits_div_le (1/2-error) (1/2-q)
  rw [computedWeight_eq]
  omega

theorem walkRowCell_encodingBits (P : Parameters) (Lgamma level clock : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) (query : WalkCell level) :
    ratEncodingBits ((P.walkRow level true clock).getD query.val 0)≤
      5*(clock+1)*(Lgamma+2) := by
  apply commonPower_encodingBits P Lgamma clock gammaBits
  · obtain ⟨factor,equation⟩ := PDROC.DataBits.endpointWalkDistribution_den_dvd P level true clock query
    refine ⟨factor*P.channelCommonDenominator,?_⟩
    rw [pow_succ,equation]
    exact Nat.mul_assoc ..
  · have nonnegative := PDROC.endpointWalkDistribution_nonneg P level true clock query
    have upper := Finset.single_le_sum
      (f:=fun state : WalkCell level => P.walkDistribution level true clock state)
      (fun state _ => PDROC.endpointWalkDistribution_nonneg P level true clock state)
      (Finset.mem_univ query)
    rw [PDROC.endpointWalkDistribution_sum] at upper
    exact PDROC.DataBits.ratNumAbs_le_den _ nonnegative upper

/-- Actual sum-finish transient values. Prefix sums share the one row
denominator before these two scalar operations; the cursor never
multiplies the bit envelope. -/
theorem sumFinish_scalar_encodingBits (P : Parameters) (Lgamma level clock count : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) (bounded : count≤2*level+1)
    (query : WalkCell level) :
    ratEncodingBits ((P.walkRow level true clock).getD query.val 0*(1/2))≤
        5*(clock+1)*(Lgamma+2)+4 ∧
      ratEncodingBits (rowPrefixSum (P.walkRow level true clock) count+
        (P.walkRow level true clock).getD query.val 0*(1/2))≤20*(clock+1)*(Lgamma+2)+8 := by
  have rowBits := walkRowCell_encodingBits P Lgamma level clock gammaBits query
  have prefixBits := walkRowPrefix_encodingBits P Lgamma level clock count gammaBits bounded
  have half : ratEncodingBits (1/2 : ℚ)=4 := by
    norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have product := PDROC.DataBits.ratEncodingBits_mul_le
    ((P.walkRow level true clock).getD query.val 0) (1/2)
  rw [half] at product
  have combined := PDROC.DataBits.ratEncodingBits_add_le
    (rowPrefixSum (P.walkRow level true clock) count)
    ((P.walkRow level true clock).getD query.val 0*(1/2))
  constructor
  · omega
  · nlinarith

/-- Numerator, denominator and actual branch-result of the original
weight block, all linear in Q and gamma bits. These are scalar facts;
all untouched live cells and registers still require caller carry. -/
theorem weightPhase_scalar_encodingBits (P : Parameters) (Lgamma m : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) (inside : m≤P.certificate.M) :
    ratEncodingBits (1/2-(P.endpointConstant m).error)≤128*(P.certificate.Q+1)*(Lgamma+2) ∧
      ratEncodingBits (1/2-P.cachedCappedError m)≤128*(P.certificate.Q+1)*(Lgamma+2) ∧
      ratEncodingBits (computedWeight (P.endpointConstant m).error (P.cachedCappedError m))≤
        128*(P.certificate.Q+1)*(Lgamma+2) := by
  let scale := (P.certificate.Q+1)*(Lgamma+2)
  have errorBits : ratEncodingBits (P.endpointConstant m).error≤40*scale := by
    simpa only [endpointConstant,scale,Nat.mul_assoc] using
      PDROC.DataBits.calibrationEndpoint_encodingBits_le P Lgamma gammaBits m inside
  have qBits : ratEncodingBits (P.cachedCappedError m)≤5*scale := by
    simpa only [scale,Nat.mul_assoc] using PDROC.DataBits.cachedCappedError_encodingBits_le P Lgamma gammaBits m
  have numerator := half_sub_scalar_encodingBits (P.endpointConstant m).error (40*scale) errorBits
  have denominator := half_sub_scalar_encodingBits (P.cachedCappedError m) (5*scale) qBits
  have weight := computedWeight_scalar_encodingBits (P.endpointConstant m).error
    (P.cachedCappedError m) (40*scale) (5*scale) errorBits qBits
  have positive : 0<scale := Nat.mul_pos (by omega) (by omega)
  simp only [Nat.mul_assoc]
  change _≤128*scale ∧ _≤128*scale ∧ _≤128*scale
  omega

end PDLower.CalibrationCompute
