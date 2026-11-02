module

public import PaperProofs.Star.PDROC_StarFirstExit_Local_003
public import PaperProofs.Star.PDROC_StarFirstExit_Local_005
public import PaperProofs.Star.PDROC_StarLRHead_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarFirstExit.Local

/-- Original selector stability on a REAL same-current/open run interval.
No supplied selection oracle and no global policy legality premise. -/
theorem chosenTarget_run_between (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (start extra : ℕ) (i : (starInstance P.tools order).Stage)
    (cursorStart : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample start).cursor = i.val)
    (liveFinish : liveStage (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (start+extra)) i)
    (portFinish : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (start+extra)).ledger.written i = none) :
    P.chosenTargetReal order kind r
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (start+extra)).history i =
      P.chosenTargetReal order kind r
        (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample start).history i := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have between := PDROC.StarLocalReview.run_live_unwritten_between_no_legal
      (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample
      start (start+extra) (start+(extra+1)) (by omega) (by omega) i cursorStart liveFinish portFinish
    exact (chosenTarget_run_succ_same_open P order kind r C accounting sample (start+extra) i
      between.1 liveFinish portFinish).trans (ih between.1 between.2)

theorem stableTarget_of_entry_target (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (entry : Entry P order kind r C accounting sample entryClock i)
    (targetEq : P.chosenTargetReal order kind r
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample entryClock).history i = some target) :
    StableTarget P order kind r C accounting sample entryClock i target := by
  intro extra
  dsimp only
  intro live port
  exact (chosenTarget_run_between P order kind r C accounting sample entryClock extra i entry.live.2 live port).trans targetEq

/-- Standard actual entry plus its SINGLE computed target value suffice;
the conditional Local.StableTarget hypothesis is discharged internally. -/
theorem actualEntry_runReviews_eq_realStop (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (entry : Entry P order kind r C accounting sample entryClock i)
    (targetEq : P.chosenTargetReal order kind r
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample entryClock).history i = some target) :
    (⨆ clock : ℕ, (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) sample clock).ledger.reviews i) =
        realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) :=
  runReviews_eq_realStop P order kind r C accounting sample entryClock i target entry
    (stableTarget_of_entry_target P order kind r C accounting sample entryClock i target entry targetEq)

theorem actualEntry_runStageObservationBill_eq (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (entry : Entry P order kind r C accounting sample entryClock i)
    (targetEq : P.chosenTargetReal order kind r
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample entryClock).history i = some target) :
    runStageObservationBill (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) i sample =
      P.channel.experiment.observationCharge
        (realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i)) :=
  runStageObservationBill_eq P order kind r C accounting sample entryClock i target entry
    (stableTarget_of_entry_target P order kind r C accounting sample entryClock i target entry targetEq)

/-- The actual first-cursor entryHistory has the SAME original computed
target as the current live/open stage; no entry stability premise is assumed. -/
theorem entryHistory_target_of_live_unwritten (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (clock : ℕ) (i : (starInstance P.tools order).Stage)
    (live : liveStage (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock) i)
    (port : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).ledger.written i = none) :
    ∃ history, entryHistory (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) i sample = some history ∧
      P.chosenTargetReal order kind r history i = P.chosenTargetReal order kind r
        (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history i := by
  classical
  have reached : ∃ n : ℕ, (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) sample n).cursor = i.val := ⟨clock, live.2⟩
  let start := Nat.find reached
  have cursorStart : (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) sample start).cursor = i.val := Nat.find_spec reached
  have before : start ≤ clock := Nat.find_min' reached live.2
  have time : start+(clock-start) = clock := Nat.add_sub_of_le before
  have target := chosenTarget_run_between P order kind r C accounting sample start (clock-start) i cursorStart
    (by simpa only [time] using live) (by simpa only [time] using port)
  rw [time] at target
  refine ⟨(run (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) sample start).history, ?_, target.symm⟩
  simp only [entryHistory, dite_eq_left reached]
  rfl

/-- The real original ideal rule selected another review at its quota:
the sample belongs to the ORIGINAL anyStarOverflow event at its real entry. -/
theorem review_at_quota_mem_anyStarOverflow (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (clock : ℕ) (i : (starInstance P.tools order).Stage) (quota : ℕ)
    (live : liveStage (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock) i)
    (port : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).ledger.written i = none)
    (selected : P.starReferenceRule order kind r none sample.1
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history = .review i)
    (reached : (quota : ℕ∞) ≤
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).ledger.reviews i) :
    sample ∈ P.anyStarOverflow order kind r quota C accounting := by
  obtain ⟨target, currentTarget, overflow⟩ := review_at_quota_current_overflow P order kind r C accounting
    sample clock i quota live port selected reached
  obtain ⟨history, atEntry, sameTarget⟩ := entryHistory_target_of_live_unwritten P order kind r C accounting
    sample clock i live port
  apply Set.mem_iUnion.mpr
  refine ⟨i, Set.mem_iUnion.mpr ⟨(P.input order).truthAt sample.2 i, ?_⟩⟩
  exact ⟨history, target, atEntry, Set.mem_univ _, sameTarget.trans currentTarget, rfl, overflow⟩

end PDROC.StarFirstExit.Local
