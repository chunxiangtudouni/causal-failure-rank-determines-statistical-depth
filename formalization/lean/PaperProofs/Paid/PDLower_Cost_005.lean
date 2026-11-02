module

public import PaperProofs.Paid.PDLower_Cost_003
public import PaperProofs.Paid.PDLower_Cost_004
public import PaperProofs.Paid.PDLower_Posterior_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics
open PaperProofs.Statistics.BinarySymmetric

namespace PDLower

universe u

theorem usageLower (P : PaperProofs.Paid.Parameters) : P.UsageLower.{u} := by
  intro fee hf C mode accounting Seed ms
  let : MeasurableSpace Seed := ms
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy hrisk
  let repairs := meanRepairCount (P.input fee hf) C.val mode accounting policy.rule ν
  let b := repairs + (P.certificate.risk : ℝ)
  let m := P.survivalMassLower
  have hm : 0 < m := P.survivalMassLower_pos
  have hd : 0 < (P.certificate.risk : ℝ) := by exact_mod_cast P.certificate.risk_pos
  have hb : 0 < b := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hd
  have hcost := expectedObservation_add_correctionCount_le P fee hf C mode accounting policy ν
  have hinformation := survivingInformationLower P fee hf C mode accounting Seed ms ν hν policy
  by_cases hhalf : 1 / 2 ≤ b / m
  · have heq : min (1 / 2) (b / m) = 1 / 2 := min_eq_left hhalf
    change ENNReal.ofReal (P.a * m) * phi (min (1 / 2) (b / m)) + _ ≤ _
    rw [heq, phi_half, mul_zero, zero_add]
    exact le_trans (le_add_left le_rfl) hcost
  · have hs := (survivingEntryClaims P fee hf C mode accounting Seed ms ν hν policy).2.2.2 hrisk
    have hδ : 0 ≤ (P.certificate.risk : ℝ) := hd.le
    have hmass : ENNReal.ofReal m ≤ ∑ stage : P.sharedInstance.Stage,
        (P.input fee hf).seededWorldLaw ν (P.survivingEntry fee hf C mode accounting policy.rule stage) := by
      calc
        _ = ENNReal.ofReal (P.certificate.stages : ℝ) * (1 - P.targetRisk) := by
          rw [show m = (P.certificate.stages : ℝ) * (1 - (P.certificate.risk : ℝ)) from rfl,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_sub _ hδ]
          norm_num [Parameters.targetRisk]
        _ = ∑ _stage : P.sharedInstance.Stage, (1 - P.targetRisk) := by
          have hcard : Fintype.card P.sharedInstance.Stage = P.certificate.stages := by
            change Fintype.card (Fin P.sharedInstance.compatibility.length) = _
            rw [Fintype.card_fin]
            exact P.stageCount_eq
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
          norm_num
        _ ≤ _ := Finset.sum_le_sum (fun stage _ => hs stage)
    have hpost : (∑ stage : P.sharedInstance.Stage,
        ∫⁻ sample, (P.survivingEntry fee hf C mode accounting policy.rule stage).indicator
          (fun sample => ENNReal.ofReal (P.paidRunPosteriorError fee hf C mode accounting policy.rule sample stage)) sample
            ∂(P.input fee hf).seededWorldLaw ν) ≤ ENNReal.ofReal b := by
      have hp := posteriorFailureAllowance P fee hf C mode accounting Seed ms ν hν policy hrisk
      apply hp.trans_eq
      change expectedRepairCount (P.input fee hf) C.val mode accounting policy.rule ν +
        ENNReal.ofReal (P.certificate.risk : ℝ) = ENNReal.ofReal (repairs + (P.certificate.risk : ℝ))
      have hrepair : ENNReal.ofReal repairs = expectedRepairCount (P.input fee hf) C.val mode accounting policy.rule ν :=
        ofReal_meanRepairCount (P.input fee hf) C.val mode accounting policy.rule policy.legal ν
      rw [ENNReal.ofReal_add (show 0 ≤ repairs from ENNReal.toReal_nonneg) hd.le, hrepair]
    have hperspective := gated_perspective ((P.input fee hf).seededWorldLaw ν)
      (fun stage => P.survivingEntry fee hf C mode accounting policy.rule stage)
      (fun stage => P.measurableSet_survivingEntry fee hf C mode accounting policy.rule policy.measurable_rule stage)
      (fun stage sample => P.paidRunPosteriorError fee hf C mode accounting policy.rule sample stage)
      (fun stage sample => (paidRunPosteriorError_range P fee hf C mode accounting policy.rule sample stage).1)
      (fun stage sample => (paidRunPosteriorError_range P fee hf C mode accounting policy.rule sample stage).2)
      (fun stage => measurable_paidRunPosteriorError P fee hf C mode accounting policy.rule policy.measurable_rule stage)
      m b hm hb (lt_of_not_ge hhalf).le hmass hpost
    have hobservation : ENNReal.ofReal (P.a * m) * phi (min (1 / 2) (b / m)) ≤
        expectedObservationBill (P.input fee hf) C.val mode accounting policy.rule ν := by
      rw [min_eq_right (lt_of_not_ge hhalf).le, ENNReal.ofReal_mul P.a_pos.le, mul_assoc]
      exact (mul_le_mul' le_rfl hperspective).trans hinformation
    exact (add_le_add hobservation le_rfl).trans hcost

end PDLower
