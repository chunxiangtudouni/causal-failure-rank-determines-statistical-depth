module

public import PaperProofs.Star.PStar_CountAllowanceLaw_033
public import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCountExpectedCost034

open Common Common.Native Parameters MeasureTheory PStarActualHalt022 PStarCountProbability019
  PStarCountStageBill032 PStarCountAllowanceLaw033
open scoped BigOperators ENNReal

theorem expected_countObservationBill_le_sum (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (countKind : kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst))
    (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1/4) :
    expectedObservationBill (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none (Seed := Unit)) (Measure.dirac ()) ≤
      ∑ stage : (starInstance P.tools order).Stage,
        prefixWeight P r stage.val * ENNReal.ofReal (P.channel.a * (Real.log (1 / stageTarget P r stage.val) + P.channel.h)) := by
  rw [expectedObservationBill_eq_sum_stage (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) (reference_legal P order kind r C qualified accounting)
    (P.measurable_starReferenceRule order kind r none) (Measure.dirac ())]
  apply Finset.sum_le_sum
  intro stage _member
  calc
    _ ≤ ∫⁻ sample : Unit × (P.input order).World, countStageAllowance P order r sample.2 stage
        ∂(P.input order).seededWorldLaw (Measure.dirac ()) :=
      lintegral_mono (fun sample => runStageObservationBill_le_allowance P order kind countKind r C qualified accounting sample stage)
    _ = ∫⁻ world : (P.input order).World, countStageAllowance P order r world stage ∂(P.input order).worldLaw :=
      lintegral_world_seededUnit (P.input order) _ (measurable_countStageAllowance P order r stage)
    _ ≤ _ := lintegral_countAllowance_le P order r positive quarter stage

theorem expectedCountObservationBill_le_weightedSum (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (countKind : kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst))
    (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1/4) :
    expectedObservationBill (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none (Seed := Unit)) (Measure.dirac ()) ≤
      ∑ stage ∈ Finset.range (P.tools+1),
        prefixWeight P r stage * ENNReal.ofReal (P.channel.a * (Real.log (1 / stageTarget P r stage) + P.channel.h)) := by
  have reindex : (∑ stage : (starInstance P.tools order).Stage,
      prefixWeight P r stage.val * ENNReal.ofReal (P.channel.a * (Real.log (1 / stageTarget P r stage.val) + P.channel.h))) =
      ∑ stage ∈ Finset.range (P.tools+1),
        prefixWeight P r stage * ENNReal.ofReal (P.channel.a * (Real.log (1 / stageTarget P r stage) + P.channel.h)) := by
    calc
      _ = ∑ stage : Fin (P.tools+1),
          prefixWeight P r stage.val * ENNReal.ofReal (P.channel.a * (Real.log (1 / stageTarget P r stage.val) + P.channel.h)) :=
        Fintype.sum_equiv (stageEquiv P.tools order) _ _ (fun _ => rfl)
      _ = _ := (Finset.sum_range (fun stage =>
        prefixWeight P r stage * ENNReal.ofReal (P.channel.a * (Real.log (1 / stageTarget P r stage) + P.channel.h)))).symm
  exact (expected_countObservationBill_le_sum P order kind countKind C qualified accounting r positive quarter).trans_eq reindex

end PaperProofs.Star.PStarCountExpectedCost034
