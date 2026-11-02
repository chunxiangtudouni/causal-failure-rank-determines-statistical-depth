module

public import PaperProofs.Star.PDROC_StarFirstExit_Local_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarFirstExit.Local

/-- Actual review is strictly before the original real stop at the CURRENT
actual selected target. No caller entry/target-stability/legality assumption. -/
theorem review_current_before_stop (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (clock : ℕ) (i : (starInstance P.tools order).Stage)
    (live : liveStage (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock) i)
    (port : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).ledger.written i = none)
    (selected : P.starReferenceRule order kind r none sample.1
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history = .review i) :
    ∃ target : ℝ, P.chosenTargetReal order kind r
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history i = some target ∧
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).ledger.reviews i <
        realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) := by
  rcases sample with ⟨⟨⟩, world⟩
  have hp := run_prefix_of_active_no_legal (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none (Seed := Unit)) ((),world) clock live.1
  have action := (actual_action P order kind r C accounting ((),world) clock i live port).symm.trans selected
  have known := prefix_currentTestInvariant P order kind r C accounting ((P.input order).truthAt world)
    (worldTapes (P.input order) world) hp i live port
  unfold NoEarlierHit at known
  cases ht : P.chosenTargetReal order kind r
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) ((),world) clock).history i with
  | none =>
    rw [ht] at action
    cases action
  | some target =>
    rw [ht] at action known
    dsimp only at action known
    have nohit : |P.channel.experiment.logOddsScore ((P.input order).reviewAt world i)
        ((run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) ((),world) clock).ledger.reviews i).toNat| <
          Real.log ((1-target)/target) := by
      by_contra absent
      simp only [ite_eq_left (le_of_not_gt absent), reduceCtorEq] at action
    refine ⟨target, ?_, ?_⟩
    · rfl
    · have count : (((run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none)
          ((),world) clock).ledger.reviews i).toNat : ℕ∞) <
          realPosteriorStop P.channel.experiment target ((P.input order).reviewAt world i) := by
        apply lt_of_not_ge
        intro early
        obtain ⟨k, hk, hit⟩ := (realStop_le_iff P.channel.experiment target ((P.input order).reviewAt world i) _).mp early
        by_cases before : k < ((run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none)
            ((),world) clock).ledger.reviews i).toNat
        · exact (not_le_of_gt (known k before)) hit
        · have eq : k = ((run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none)
              ((),world) clock).ledger.reviews i).toNat := by omega
          rw [eq] at hit
          exact (not_le_of_gt nohit) hit
      simpa only [prefix_reviews_natCast_toNat (P.input order) C .uncapped accounting
        (P.starReferenceRule order kind r none) () ((P.input order).truthAt world)
        (worldTapes (P.input order) world) hp i] using count

theorem review_at_quota_current_overflow (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (clock : ℕ) (i : (starInstance P.tools order).Stage) (quota : ℕ)
    (live : liveStage (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock) i)
    (port : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).ledger.written i = none)
    (selected : P.starReferenceRule order kind r none sample.1
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history = .review i)
    (reached : (quota : ℕ∞) ≤
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).ledger.reviews i) :
    ∃ target : ℝ, P.chosenTargetReal order kind r
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history i = some target ∧
      (quota : ℕ∞) < realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) := by
  obtain ⟨target, ht, before⟩ := review_current_before_stop P order kind r C accounting sample clock i live port selected
  exact ⟨target, ht, reached.trans_lt before⟩

end PDROC.StarFirstExit.Local
