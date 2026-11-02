module

public import PaperProofs.Star.PStar_CountErrorProbability_024
public import PaperProofs.Star.PStar_CurrentFailure_020
public import PaperProofs.Star.PStar_EarlyHalt_021

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCountIdealRisk025

open Common Common.Native Parameters MeasureTheory PStarLR PStarEarlyHalt021
  PStarCurrentFailure020 PStarActualHalt022 PStarCountTestErrors023 PStarCountErrorProbability024

theorem earlyRetained_halted_failure_all_errors (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (early : C.IsEarlyRetained)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .earlyRetained r none)
      seed truth tapes n state) (halted : state.halted = true) (failed : ¬state.ledger.success C) :
    ∀ stage : (starInstance P.tools order).Stage,
      state.ledger.written stage = some (!state.ledger.truth stage) := by
  classical
  have complete := early_halted_prefix_allWritten P order r C .uncapped accounting seed truth tapes path halted
  have criterion := retained_halted_card_criterion P order .earlyRetained (by decide) r none C
    early.2.1 early.2.2 .uncapped accounting seed truth tapes path halted complete
  have bad : ¬(PaperProofs.Retained.ordinaryMismatches state.ledger).card ≤ P.tools := fun good => failed (criterion.1.mpr good)
  have full : PaperProofs.Retained.ordinaryMismatches state.ledger =
      (Finset.univ : Finset (starInstance P.tools order).Stage) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    have total : (Finset.univ : Finset (starInstance P.tools order).Stage).card = P.tools+1 := by
      simp only [Finset.card_univ, Instance.Stage, Fintype.card_fin]
      exact stageCount_eq P.tools order
    rw [total]
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge bad)
  intro stage
  apply (PaperProofs.Retained.mem_ordinaryMismatches state.ledger stage).mp
  rw [full]
  exact Finset.mem_univ _

/-- EXACT original C08 uncapped ideal risk field: both retained orders and
singleton-first current, actual fixed scripts and all original contracts.
Termination and independent error gating are proved internally. -/
theorem countIdealRisk (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (countKind : kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst))
    (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1/4) :
    risk (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none (Seed := Unit))
      (Measure.dirac ()) ≤ ENNReal.ofReal r := by
  classical
  have domination : {sample : Unit × (P.input order).World |
      ¬runSuccess (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample}
      ≤ᵐ[(P.input order).seededWorldLaw (Measure.dirac ())]
      {sample : Unit × (P.input order).World | sample.2 ∈ countErrorEvent P order r} := by
    filter_upwards [original_halts_ae P order kind r positive quarter C qualified accounting] with sample eventuallyHalted
    intro failure
    rcases sample with ⟨⟨⟩, world⟩
    obtain ⟨n, halted⟩ := eventuallyHalted
    obtain ⟨clock, _bound, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) (reference_legal P order kind r C qualified accounting) ((), world) n
    have failed : ¬(run (P.input order) C .uncapped accounting
        (P.starReferenceRule order kind r none) ((), world) n).ledger.success C := by
      intro success
      exact failure ⟨n, halted, success⟩
    have allWrong : ∀ stage : (starInstance P.tools order).Stage,
        (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) ((),world) n).ledger.written stage =
          some (!(run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) ((),world) n).ledger.truth stage) := by
      rcases countKind with rfl | ⟨rfl, rfl⟩
      · exact earlyRetained_halted_failure_all_errors P order r C qualified accounting () _ _ path halted failed
      · exact singletonsFirst_halted_failure_all_errors P r C qualified.1 accounting () _ _ path halted failed
    change ∀ stage : (starInstance P.tools order).Stage,
      (P.channel.symmetricHittingTest (realTargetIndex P.channel (PStarCountProbability019.stageTarget P r stage.val))).rule.decision ()
        ((P.input order).reviewAt world stage) ≠ (P.input order).truthAt world stage
    exact count_all_errors_testErrors P order kind countKind r C qualified accounting world path allWrong
  exact (measure_mono_ae domination).trans (countErrorEvent_seeded_le P order r positive quarter)

end PaperProofs.Star.PStarCountIdealRisk025
