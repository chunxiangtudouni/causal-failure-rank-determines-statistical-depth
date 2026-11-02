module

public import Paid.PDLower_CalibrationCompute_IntermediateBits_056
public import Paid.PDLower_CalibrationCompute_SumValue_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open scoped BigOperators
open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDLower.CalibrationCompute

/-- Summation of a row prefix keeps its one original common denominator.
The cursor does not multiply the numerator/denominator bit envelope. -/
theorem walkRowPrefix_denominator (P : Parameters) (level clock count : ℕ)
    (bounded : count≤2*level+1) :
    (rowPrefixSum (P.walkRow level true clock) count).den ∣ P.channelCommonDenominator^clock := by
  apply PDROC.DataBits.sum_den_dvd
  intro index member
  have inside : index<2*level+1 := (Finset.mem_range.mp member).trans_le bounded
  exact PDROC.DataBits.endpointWalkDistribution_den_dvd P level true clock ⟨index,inside⟩

theorem walkRowPrefix_bounds (P : Parameters) (level clock count : ℕ)
    (bounded : count≤2*level+1) :
    0≤rowPrefixSum (P.walkRow level true clock) count ∧
      rowPrefixSum (P.walkRow level true clock) count≤1 := by
  have nonnegative (index : ℕ) (inside : index<2*level+1) :
      0≤(P.walkRow level true clock).getD index 0 :=
    PDROC.endpointWalkDistribution_nonneg P level true clock ⟨index,inside⟩
  have whole : rowPrefixSum (P.walkRow level true clock) (2*level+1)=1 := by
    have normalized := PDROC.endpointWalkDistribution_sum P level true clock
    change (∑ state : WalkCell level,(P.walkRow level true clock).getD state.val 0)=1 at normalized
    exact (Fin.sum_univ_eq_sum_range
      (fun index : ℕ => (P.walkRow level true clock).getD index 0) (2*level+1)).symm.trans normalized
  constructor
  · apply Finset.sum_nonneg
    intro index member
    exact nonnegative index ((Finset.mem_range.mp member).trans_le bounded)
  · rw [←whole]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono bounded)
    intro index member _outside
    exact nonnegative index (Finset.mem_range.mp member)

theorem walkRowPrefix_encodingBits (P : Parameters) (Lgamma level clock count : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) (bounded : count≤2*level+1) :
    ratEncodingBits (rowPrefixSum (P.walkRow level true clock) count)≤5*(clock+1)*(Lgamma+2) := by
  apply commonPower_encodingBits P Lgamma clock gammaBits
  · obtain ⟨factor,equation⟩ := walkRowPrefix_denominator P level clock count bounded
    refine ⟨factor*P.channelCommonDenominator,?_⟩
    rw [pow_succ,equation]
    exact Nat.mul_assoc ..
  · have bounds := walkRowPrefix_bounds P level clock count bounded
    exact PDROC.DataBits.ratNumAbs_le_den _ bounds.1 bounds.2

end PDLower.CalibrationCompute
