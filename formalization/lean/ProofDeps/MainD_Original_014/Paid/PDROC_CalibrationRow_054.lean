module

public import Paid.PDROC_CalibrationRow_039
public import Paid.PDLower_CalibrationCompute_IntermediateBits_056

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.CalibrationRow

open scoped BigOperators
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem walkRow_cell_unit (P : Parameters) (level clock : ℕ) (query : WalkCell level) :
    0≤(P.walkRow level true clock).getD query.val 0 ∧
      (P.walkRow level true clock).getD query.val 0≤1 := by
  have lower := PDROC.endpointWalkDistribution_nonneg P level true clock query
  have upper := Finset.single_le_sum
    (f:=fun state : WalkCell level => P.walkDistribution level true clock state)
    (fun state _ => PDROC.endpointWalkDistribution_nonneg P level true clock state) (Finset.mem_univ query)
  rw [PDROC.endpointWalkDistribution_sum] at upper
  exact ⟨lower,upper⟩

/-- Uniform denominator for actual old physical read rows. The exponent
is Q+1, independent of the row width and the number of visited cells. -/
theorem walkRow_denominator_Q (P : Parameters) (level clock : ℕ) (bound : clock≤P.certificate.Q)
    (query : WalkCell level) :
    ((P.walkRow level true clock).getD query.val 0).den ∣ P.channelCommonDenominator^(P.certificate.Q+1) :=
  (PDROC.DataBits.endpointWalkDistribution_den_dvd P level true clock query).trans
    (pow_dvd_pow P.channelCommonDenominator (by omega))

theorem walkRow_encodingBits_Q (P : Parameters) (Lgamma level clock : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) (bound : clock≤P.certificate.Q)
    (query : WalkCell level) :
    ratEncodingBits ((P.walkRow level true clock).getD query.val 0)≤5*(P.certificate.Q+1)*(Lgamma+2) := by
  have unit := walkRow_cell_unit P level clock query
  exact commonPower_encodingBits P Lgamma P.certificate.Q gammaBits _
    (walkRow_denominator_Q P level clock bound query) (PDROC.DataBits.ratNumAbs_le_den _ unit.1 unit.2)

theorem rowScatterPrefix_denominator_Q (P : Parameters) (level clock cursor : ℕ)
    (bound : clock≤P.certificate.Q) (query : WalkCell level) :
    ((rowScatterPrefix P level (P.walkRow level true clock) cursor).getD query.val 0).den ∣
      P.channelCommonDenominator^(P.certificate.Q+1) :=
  (rowScatterPrefix_denominator P level clock cursor query.val
    (by simpa only [rowScatterPrefix_size] using query.isLt)).trans
      (pow_dvd_pow P.channelCommonDenominator (Nat.add_le_add_right bound 1))

theorem rowScatterPrefix_encodingBits_Q (P : Parameters) (Lgamma level clock cursor : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) (bound : clock≤P.certificate.Q)
    (query : WalkCell level) :
    ratEncodingBits ((rowScatterPrefix P level (P.walkRow level true clock) cursor).getD query.val 0)≤
      5*(P.certificate.Q+1)*(Lgamma+2) :=
  (rowScatterPrefix_encodingBits P Lgamma level clock cursor gammaBits query).trans
    (Nat.mul_le_mul_right (Lgamma+2) (Nat.mul_le_mul_left 5 (Nat.add_le_add_right bound 1)))

theorem rowLeftPrefix_denominator_Q (P : Parameters) (level clock cursor : ℕ)
    (bound : clock≤P.certificate.Q) (inside : cursor<2*level+1) (query : WalkCell level) :
    ((rowLeftPrefix P level clock cursor inside).getD query.val 0).den ∣
      P.channelCommonDenominator^(P.certificate.Q+1) :=
  (rowLeftPrefix_denominator P level clock cursor inside query.val
    (by simpa only [rowLeftPrefix,PDROC.endpointArrayBump_size,rowScatterPrefix_size] using query.isLt)).trans
      (pow_dvd_pow P.channelCommonDenominator (Nat.add_le_add_right bound 1))

theorem rowLeftPrefix_encodingBits_Q (P : Parameters) (Lgamma level clock cursor : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) (bound : clock≤P.certificate.Q)
    (inside : cursor<2*level+1) (query : WalkCell level) :
    ratEncodingBits ((rowLeftPrefix P level clock cursor inside).getD query.val 0)≤
      5*(P.certificate.Q+1)*(Lgamma+2) :=
  (rowLeftPrefix_encodingBits P Lgamma level clock cursor gammaBits inside query).trans
    (Nat.mul_le_mul_right (Lgamma+2) (Nat.mul_le_mul_left 5 (Nat.add_le_add_right bound 1)))

/-- Direct bridge to the physical heap reader at any stable Q gate;
this bounds a produced row value, not arbitrary incoming caller cells. -/
theorem StepData.read_cell_bits (P : Parameters) (Lgamma base level clock : ℕ) (state : State)
    (data : StepData P base level clock state) (bound : clock≤P.certificate.Q)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) (query : WalkCell level) :
    ∃ value : ℚ,state.heap ((rowPointers base P.certificate.M clock).1+query.val)=.rational value ∧
      value.den ∣ P.channelCommonDenominator^(P.certificate.Q+1) ∧
      ratEncodingBits value≤5*(P.certificate.Q+1)*(Lgamma+2) := by
  exact ⟨_,data.readRow.value query.val (by simpa only [PDROC.endpointWalkRow_size] using query.isLt),
    walkRow_denominator_Q P level clock bound query,walkRow_encodingBits_Q P Lgamma level clock gammaBits bound query⟩

end PDROC.CalibrationRow
