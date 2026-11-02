module

public import Paid.PDROC_CalibrationRow_ScatterOperands_001
public import Paid.PDROC_CalibrationRow_Scatter_007
public import Paid.PDLower_CalibrationCompute_IntermediateBits_056
public import PaperProofs.Paid.PDROC_DataBits_Mixture_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open scoped BigOperators

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute

/-- A finite, exact family for the genuinely assigned scatter values.
The first-letter transient is separate from every completed cell pair. -/
inductive Catalog (P : Parameters) (base level clock : ℕ) : Cell → Prop where
  | natural (value : ℕ) (bound : value ≤ resultBase base P.certificate.M) :
      Catalog P base level clock (.natural value)
  | read (query : WalkCell level) :
      Catalog P base level clock (.rational ((P.walkRow level true clock).getD query.val 0))
  | channel (letter : Fin 2) :
      Catalog P base level clock (.rational (P.experiment.channel true letter))
  | product (query : WalkCell level) (letter : Fin 2) :
      Catalog P base level clock
        (.rational ((P.walkRow level true clock).getD query.val 0 * P.experiment.channel true letter))
  | partialRow (cursor : ℕ) (bound : cursor ≤ 2 * level + 1) (query : WalkCell level) :
      Catalog P base level clock
        (.rational ((rowScatterPrefix P level (P.walkRow level true clock) cursor).getD query.val 0))
  | afterLeft (cursor : ℕ) (inside : cursor < 2 * level + 1) (query : WalkCell level) :
      Catalog P base level clock (.rational ((rowLeftPrefix P level clock cursor inside).getD query.val 0))

def catalogBudget (P : Parameters) (base clock Lgamma : ℕ) : ℕ :=
  max (1 + natBits (resultBase base P.certificate.M)) (1 + 10 * (clock + 1) * (Lgamma + 2))

/-- Thin use of the frozen common-power lemma and original row facts.
There is no new denominator induction or iteration over scattered cells. -/
theorem read_encodingBits (P : Parameters) (Lgamma level clock : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma ≤ Lgamma) (query : WalkCell level) :
    ratEncodingBits ((P.walkRow level true clock).getD query.val 0) ≤
      5 * (clock + 1) * (Lgamma + 2) := by
  change ratEncodingBits (P.walkDistribution level true clock query) ≤ _
  have unit := Finset.single_le_sum
    (f := fun state : WalkCell level => P.walkDistribution level true clock state)
    (fun state _ => PDROC.endpointWalkDistribution_nonneg P level true clock state)
    (Finset.mem_univ query)
  rw [PDROC.endpointWalkDistribution_sum] at unit
  apply commonPower_encodingBits P Lgamma clock gammaBits
  · exact (PDROC.DataBits.endpointWalkDistribution_den_dvd P level true clock query).trans
      (pow_dvd_pow P.channelCommonDenominator (Nat.le_succ clock))
  · exact PDROC.DataBits.ratNumAbs_le_den _
      (PDROC.endpointWalkDistribution_nonneg P level true clock query) unit

theorem channel_encodingBits (P : Parameters) (Lgamma clock : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma ≤ Lgamma) (letter : Fin 2) :
    ratEncodingBits (P.experiment.channel true letter) ≤ 5 * (clock + 1) * (Lgamma + 2) := by
  have unit : P.experiment.channel true letter ≤ 1 := by
    fin_cases letter
    · change (1 / 2 - P.certificate.gamma : ℚ) ≤ 1
      linarith [P.certificate.gamma_pos]
    · change (1 / 2 + P.certificate.gamma : ℚ) ≤ 1
      linarith [P.certificate.gamma_le_quarter]
  apply commonPower_encodingBits P Lgamma clock gammaBits
  · exact (PDROC.DataBits.channel_den_dvd P true letter).trans
      (by simpa only [pow_one] using
        pow_dvd_pow P.channelCommonDenominator (by omega : 1 ≤ clock + 1))
  · exact PDROC.DataBits.ratNumAbs_le_den _ (P.experiment.channel_pos true letter).le unit

theorem Catalog.bits (P : Parameters) (base level clock Lgamma : ℕ)
    (gammaBits : ratEncodingBits P.certificate.gamma ≤ Lgamma)
    (value : Cell) (source : Catalog P base level clock value) :
    value.bits ≤ catalogBudget P base clock Lgamma := by
  have scale : 5 * (clock + 1) * (Lgamma + 2) ≤ 10 * (clock + 1) * (Lgamma + 2) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 5 ≤ 10))
  have rational (q : ℚ) (bound : ratEncodingBits q ≤ 10 * (clock + 1) * (Lgamma + 2)) :
      (Cell.rational q).bits ≤ catalogBudget P base clock Lgamma :=
    (Nat.add_le_add_left bound 1).trans (Nat.le_max_right _ _)
  cases source with
  | natural number bound =>
      exact (Nat.add_le_add_left (PDROC.DataBits.natBits_mono bound) 1).trans (Nat.le_max_left _ _)
  | read query => exact rational _ ((read_encodingBits P Lgamma level clock gammaBits query).trans scale)
  | channel letter => exact rational _ ((channel_encodingBits P Lgamma clock gammaBits letter).trans scale)
  | product query letter =>
      apply rational
      calc
        _ ≤ ratEncodingBits ((P.walkRow level true clock).getD query.val 0) +
            ratEncodingBits (P.experiment.channel true letter) := PDROC.DataBits.ratEncodingBits_mul_le _ _
        _ ≤ 5 * (clock + 1) * (Lgamma + 2) + 5 * (clock + 1) * (Lgamma + 2) :=
          Nat.add_le_add (read_encodingBits P Lgamma level clock gammaBits query)
            (channel_encodingBits P Lgamma clock gammaBits letter)
        _ = 10 * (clock + 1) * (Lgamma + 2) := by ring
  | partialRow cursor _ query =>
      exact rational _ ((rowScatterPrefix_encodingBits P Lgamma level clock cursor gammaBits query).trans scale)
  | afterLeft cursor inside query =>
      exact rational _ ((rowLeftPrefix_encodingBits P Lgamma level clock cursor gammaBits inside query).trans scale)

end PDROC.CalibrationRow.ScatterOperands
