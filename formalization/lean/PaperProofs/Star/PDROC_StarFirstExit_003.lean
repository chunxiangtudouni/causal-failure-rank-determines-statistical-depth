module

public import PaperProofs.Star.PDROC_StarFirstExit_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarFirstExit

theorem realStop_eq_of_first (E : PaperProofs.Statistics.BinaryExperiment) (target : ℝ)
    (tape : E.Tape) (n : ℕ)
    (hit : Real.log ((1-target)/target) ≤ |E.logOddsScore tape n|)
    (before : ∀ k : ℕ, k < n → |E.logOddsScore tape k| < Real.log ((1-target)/target)) :
    realPosteriorStop E target tape = (n : ℕ∞) := by
  unfold realPosteriorStop
  apply le_antisymm
  · exact sInf_le ⟨n, rfl, hit⟩
  · apply le_sInf
    rintro t ⟨k, rfl, hk⟩
    have hnk : n ≤ k := by
      by_contra absent
      exact (not_le_of_gt (before k (Nat.lt_of_not_ge absent))) hk
    exact_mod_cast hnk

theorem prefix_firstExit (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (r : ℝ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order))
    (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {s : State (starInstance P.tools order)}
    (hp : Prefix (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none (Seed := Unit)) () truth tapes n s)
    (i : (starInstance P.tools order).Stage) (bit : Bool)
    (live : liveStage s i) (port : s.ledger.written i = none)
    (write : P.starReferenceRule order kind r none () s.history = .write i bit) :
    match P.chosenTargetReal order kind r s.history i with
    | none => s.ledger.reviews i = 0 ∧ bit = false
    | some target => realPosteriorStop P.channel.experiment target (tapes i) =
        ((s.ledger.reviews i).toNat : ℕ∞) ∧
        bit = decide (0 ≤ P.channel.experiment.logOddsScore (tapes i) (s.ledger.reviews i).toNat) := by
  have action := (rule_testing_of_live_unwritten P order kind r C accounting truth tapes hp i live port).symm.trans write
  rw [testingAction_actual P order kind r C accounting truth tapes hp i] at action
  have known := prefix_currentTestInvariant P order kind r C accounting truth tapes hp i live port
  unfold NoEarlierHit at known
  cases ht : P.chosenTargetReal order kind r s.history i with
  | none =>
    rw [ht] at known action
    cases action
    exact ⟨known, rfl⟩
  | some target =>
    rw [ht] at known action
    dsimp only at known action
    by_cases hit : Real.log ((1-target)/target) ≤
        |P.channel.experiment.logOddsScore (tapes i) (s.ledger.reviews i).toNat|
    · simp only [ite_eq_left hit] at action
      exact ⟨realStop_eq_of_first P.channel.experiment target (tapes i) _ hit known,
        (Action.write.inj action).2.symm⟩
    · simp only [ite_eq_right hit] at action
      cases action

/-- Exact original all-order/all-kind/all-stage ReferenceRealFirstExit.
No LegalRule, target-stability, finite ET, performance or stopping premise. -/
theorem referenceRealFirstExit (P : PaperProofs.Star.Parameters) : P.ReferenceRealFirstExit := by
  intro order kind C _contracts accounting r _hr _hquarter sample n i bit
  rcases sample with ⟨⟨⟩, world⟩
  dsimp only
  intro live port write
  have hp := run_prefix_of_active_no_legal (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none (Seed := Unit)) ((), world) n live.1
  exact prefix_firstExit P order kind r C accounting ((P.input order).truthAt world)
    (worldTapes (P.input order) world) hp i bit live port write

end PDROC.StarFirstExit
