module

public import Paid.PDLower_CalibrationCompute_IntermediateLeft_055

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDLower.CalibrationCompute

theorem commonPower_encodingBits (P : Parameters) (Lgamma clock : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) (q : ℚ)
    (denominator : q.den ∣ P.channelCommonDenominator^(clock+1))
    (numerator : q.num.natAbs≤q.den) :
    ratEncodingBits q≤5*(clock+1)*(Lgamma+2) := by
  have denBits := PDROC.DataBits.ratDenBits_le_of_dvd
    (pow_pos (PDROC.DataBits.channelCommonDenominator_pos P) (clock+1)) denominator
  have commonBits := PDROC.DataBits.channelCommonDenominator_bits P Lgamma gammaBits
  have powerBits := PDROC.DataBits.natBits_pow_le P.channelCommonDenominator (clock+1)
  have multiplied := Nat.mul_le_mul_left (clock+1) commonBits
  have numBits : ratNumBits q≤ratDenBits q := PDROC.DataBits.natBits_mono numerator
  have positive : 0<(clock+1)*(Lgamma+2) := Nat.mul_pos (by omega) (by omega)
  unfold ratEncodingBits
  nlinarith

/-- In particular the original operand envelope remains LINEAR in Q,
with no hidden number-of-scattered-cells multiplier. -/
theorem rowScatterPrefix_encodingBits (P : Parameters) (Lgamma level clock cursor : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) (query : WalkCell level) :
    ratEncodingBits ((rowScatterPrefix P level (P.walkRow level true clock) cursor).getD query.val 0)≤
      5*(clock+1)*(Lgamma+2) := by
  apply commonPower_encodingBits P Lgamma clock gammaBits
  · exact rowScatterPrefix_denominator P level clock cursor query.val
      (by simpa only [rowScatterPrefix_size] using query.isLt)
  · exact rowScatterPrefix_numAbs_le_den P level clock cursor query

theorem rowLeftPrefix_encodingBits (P : Parameters) (Lgamma level clock cursor : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma) (inside : cursor<2*level+1)
    (query : WalkCell level) :
    ratEncodingBits ((rowLeftPrefix P level clock cursor inside).getD query.val 0)≤
      5*(clock+1)*(Lgamma+2) := by
  apply commonPower_encodingBits P Lgamma clock gammaBits
  · exact rowLeftPrefix_denominator P level clock cursor inside query.val
      (by simpa only [rowLeftPrefix,PDROC.endpointArrayBump_size,rowScatterPrefix_size] using query.isLt)
  · exact rowLeftPrefix_numAbs_le_den P level clock cursor inside query

end PDLower.CalibrationCompute
