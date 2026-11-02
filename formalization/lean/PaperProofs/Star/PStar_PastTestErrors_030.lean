module

public import PaperProofs.Star.PStar_CountTestErrors_023

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarPastTestErrors030

open Common Common.Native Parameters PStarLR PStarActualHalt022 PStarTargetGates013
  PStarCountProbability019 PStarCountTestErrors023

set_option backward.isDefEq.respectTransparency.types false in
theorem count_past_errors_testErrors (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (countKind : kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst))
    (r : ℝ) (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (world : (P.input order).World)
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none)
      () ((P.input order).truthAt world) (worldTapes (P.input order) world) n state)
    (boundary : ℕ) (allWrong : ∀ stage : (starInstance P.tools order).Stage, stage.val < boundary →
      state.ledger.written stage = some (!state.ledger.truth stage)) :
    ∀ stage : (starInstance P.tools order).Stage, stage.val < boundary →
      (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r stage.val))).rule.decision ()
        ((P.input order).reviewAt world stage) ≠ (P.input order).truthAt world stage := by
  classical
  have early : C.reporting = .early := by
    cases kind with
    | current => exact qualified.1
    | earlyRetained => exact qualified.1
    | lateRetained => rcases countKind with impossible | ⟨impossible, _⟩ <;> cases impossible
  have legal := reference_legal P order kind r C qualified accounting
  have endTruth := prefix_truth (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none)
    () ((P.input order).truthAt world) (worldTapes (P.input order) world) path
  intro stage included
  obtain ⟨clock, old, _before, oldPath, active, write⟩ := prefix_written_has_write (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) () ((P.input order).truthAt world) (worldTapes (P.input order) world)
    path stage (!state.ledger.truth stage) (allWrong stage included)
  obtain ⟨next, step⟩ := legal () _ _ clock old oldPath active
  rw [write] at step
  have live : liveStage old stage := by cases step with | write _ _ live _ _ => exact live
  have port : old.ledger.written stage = none := by cases step with | write _ _ _ port _ => exact port
  have oldTruth := prefix_truth (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none)
    () ((P.input order).truthAt world) (worldTapes (P.input order) world) oldPath
  have pastWrong : ∀ earlier : (starInstance P.tools order).Stage, earlier.val < stage.val →
      old.ledger.written earlier = some (!old.ledger.truth earlier) := by
    intro earlier before
    have known := prefix_pastWritten (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) () ((P.input order).truthAt world) (worldTapes (P.input order) world)
      oldPath earlier (by rwa [live.2])
    obtain ⟨bit, written⟩ := Option.ne_none_iff_exists'.mp known
    have equal := prefix_written_agree (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) legal () ((P.input order).truthAt world) (worldTapes (P.input order) world)
      oldPath path earlier bit (!state.ledger.truth earlier) written (allWrong earlier (before.trans included))
    rw [equal, endTruth] at written
    rw [oldTruth]
    exact written
  have target := countChosenTarget_on_prefix P order kind countKind r none C early .uncapped accounting
    () ((P.input order).truthAt world) (worldTapes (P.input order) world) oldPath stage live.2
  rw [ite_eq_left pastWrong] at target
  have decision := prefix_write_test_decision P order kind r C accounting ((P.input order).truthAt world)
    (worldTapes (P.input order) world) oldPath stage (!state.ledger.truth stage) live port write
    (stageTarget P r stage.val) target
  rw [endTruth] at decision
  change (!(P.input order).truthAt world stage) =
    (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r stage.val))).rule.decision ()
      ((P.input order).reviewAt world stage) at decision
  intro correct
  rw [correct] at decision
  cases actual : (P.input order).truthAt world stage <;> simp [actual] at decision

end PaperProofs.Star.PStarPastTestErrors030
