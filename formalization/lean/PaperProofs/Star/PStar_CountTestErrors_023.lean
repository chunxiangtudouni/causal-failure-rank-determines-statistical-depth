module

public import PaperProofs.Star.PStar_ActualHalt_022
public import PaperProofs.Star.PStar_CountProbability_019
public import PaperProofs.Star.PStar_TargetGates_013
public import PaperProofs.Star.PStarLR_GlobalRisk_022

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCountTestErrors023

open Common Common.Native Parameters PStarLR PStarActualHalt022 PStarTargetGates013 PStarCountProbability019

theorem prefix_written_agree {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*} (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {m n : ℕ} {left right : State I}
    (leftPath : Prefix input C mode accounting rule seed truth tapes m left)
    (rightPath : Prefix input C mode accounting rule seed truth tapes n right)
    (stage : I.Stage) (leftBit rightBit : Bool)
    (leftWrite : left.ledger.written stage = some leftBit)
    (rightWrite : right.ledger.written stage = some rightBit) : leftBit = rightBit := by
  have leftRun := prefix_eq_run input C mode accounting rule seed truth tapes leftPath
  have rightRun := prefix_eq_run input C mode accounting rule seed truth tapes rightPath
  exact run_written_agree input C mode accounting rule legal (seed, replayWorld input truth tapes)
    m n stage leftBit rightBit (by rw [leftRun]; exact leftWrite) (by rw [rightRun]; exact rightWrite)

/- Actual first-exit write identifies the chosen fixed test's decision,
without a finite-ET or target-stability assumption. -/
set_option backward.isDefEq.respectTransparency.types false in
theorem prefix_write_test_decision (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none)
      () truth tapes n state) (stage : (starInstance P.tools order).Stage) (bit : Bool)
    (live : liveStage state stage) (port : state.ledger.written stage = none)
    (write : P.starReferenceRule order kind r none () state.history = .write stage bit)
    (target : ℝ) (chosen : P.chosenTargetReal order kind r state.history stage = some target) :
    bit = (P.channel.symmetricHittingTest (realTargetIndex P.channel target)).rule.decision () (tapes stage) := by
  have actual := PDROC.StarFirstExit.prefix_firstExit P order kind r C accounting truth tapes path stage bit live port write
  rw [chosen] at actual
  have testDecision := realTarget_test_decision P.channel target (tapes stage) _ actual.1
  exact actual.2.trans testDecision.symm

/- If an actual completed prefix contains errors in every ordinary port,
then each ORIGINAL count test really errs on its own independent tape. The
past-error gate is proved from immutable actual writes, not postulated. -/
set_option backward.isDefEq.respectTransparency.types false in
theorem count_all_errors_testErrors (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (countKind : kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst))
    (r : ℝ) (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (world : (P.input order).World)
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none)
      () ((P.input order).truthAt world) (worldTapes (P.input order) world) n state)
    (allWrong : ∀ stage : (starInstance P.tools order).Stage,
      state.ledger.written stage = some (!state.ledger.truth stage)) :
    ∀ stage : (starInstance P.tools order).Stage,
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
  intro stage
  obtain ⟨clock, old, _before, oldPath, active, write⟩ := prefix_written_has_write (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) () ((P.input order).truthAt world) (worldTapes (P.input order) world)
    path stage (!state.ledger.truth stage) (allWrong stage)
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
      oldPath path earlier bit (!state.ledger.truth earlier) written (allWrong earlier)
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

end PaperProofs.Star.PStarCountTestErrors023
