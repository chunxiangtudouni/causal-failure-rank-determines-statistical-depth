module

public import PaperProofs.Star.PStar_UniversalTestErrors_026

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarUniversalHeadError035

open Common Common.Native Parameters PStarLR PStarCurrentLegality006 PStarCountTestErrors023

set_option backward.isDefEq.respectTransparency.types false in
theorem universal_written_error_testError (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .universalFirst))
    (accounting : NormalAccounting (starInstance P.tools .universalFirst)) (world : (P.input .universalFirst).World)
    {n : ℕ} {state : State (starInstance P.tools .universalFirst)}
    (path : Prefix (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
      (worldTapes (P.input .universalFirst) world) n state)
    (wrong : state.ledger.written (universalStage P.tools .universalFirst) =
      some (!state.ledger.truth (universalStage P.tools .universalFirst))) :
    (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1))).rule.decision ()
      ((P.input .universalFirst).reviewAt world (universalStage P.tools .universalFirst)) ≠
        (P.input .universalFirst).truthAt world (universalStage P.tools .universalFirst) := by
  let stage := universalStage P.tools .universalFirst
  obtain ⟨clock, old, _before, oldPath, active, write⟩ := prefix_written_has_write (P.input .universalFirst) C .uncapped accounting
    (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
    (worldTapes (P.input .universalFirst) world) path stage (!state.ledger.truth stage) wrong
  have legal := current_legal_uncapped P .universalFirst r none C accounting (Seed := Unit)
  obtain ⟨next, step⟩ := legal () _ _ clock old oldPath active
  rw [write] at step
  have live : liveStage old stage := by cases step with | write _ _ live _ _ => exact live
  have port : old.ledger.written stage = none := by cases step with | write _ _ _ port _ => exact port
  have chosen : P.chosenTargetReal .universalFirst .current r old.history stage = some (starTargetReal r 1) := by
    simp only [stage, Parameters.chosenTargetReal, stageLabel_universal]
  have decision := prefix_write_test_decision P .universalFirst .current r C accounting
    ((P.input .universalFirst).truthAt world) (worldTapes (P.input .universalFirst) world) oldPath
    stage (!state.ledger.truth stage) live port write (starTargetReal r 1) chosen
  have truths := prefix_truth (P.input .universalFirst) C .uncapped accounting
    (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
    (worldTapes (P.input .universalFirst) world) path
  rw [truths] at decision
  change (!(P.input .universalFirst).truthAt world stage) =
    (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1))).rule.decision ()
      ((P.input .universalFirst).reviewAt world stage) at decision
  intro correct
  rw [correct] at decision
  dsimp only [stage] at decision
  cases actual : (P.input .universalFirst).truthAt world (universalStage P.tools .universalFirst) <;> simp [actual] at decision

theorem chosenTarget_Universal_cases (P : PaperProofs.Star.Parameters) (r : ℝ)
    (history : List (VisibleEvent (starInstance P.tools .universalFirst)))
    (stage : (starInstance P.tools .universalFirst).Stage) (target : ℝ)
    (chosen : P.chosenTargetReal .universalFirst .current r history stage = some target) :
    (stage = universalStage P.tools .universalFirst ∧ target = starTargetReal r 1) ∨
    (stage = singletonStage P.tools .universalFirst P.firstTool ∧
      reportedError history (universalStage P.tools .universalFirst) = true ∧
      target = min (1/4) (r / starTargetReal r 1)) := by
  classical
  cases label : stageLabel P.tools .universalFirst stage with
  | none =>
    simp only [Parameters.chosenTargetReal, label] at chosen
    exact Or.inl ⟨stageLabel_injective P.tools .universalFirst (label.trans (stageLabel_universal _ _).symm),
      (Option.some.inj chosen).symm⟩
  | some tool =>
    simp only [Parameters.chosenTargetReal, label] at chosen
    split at chosen
    · rename_i trigger
      have zero : tool.val = 0 := by
        by_contra nonzero
        simp only [nonzero, decide_false, Bool.false_and, Bool.false_eq_true] at trigger
      have reported : reportedError history (universalStage P.tools .universalFirst) = true := by
        simpa only [zero, decide_true, Bool.true_and] using trigger
      have sameTool : tool = P.firstTool := Fin.ext zero
      exact Or.inr ⟨stageLabel_injective P.tools .universalFirst
        (label.trans ((congrArg some sameTool).trans (stageLabel_singleton _ _ _).symm)), reported,
        (Option.some.inj chosen).symm⟩
    · cases chosen

end PaperProofs.Star.PStarUniversalHeadError035
