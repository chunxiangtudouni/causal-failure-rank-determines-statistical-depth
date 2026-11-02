module

public import PaperProofs.Star.PStar_CountTestErrors_023

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarUniversalTestErrors026

open Common Common.Native Parameters PStarLR PStarCurrentLegality006
  PStarTargetGates013 PStarCountTestErrors023

set_option backward.isDefEq.respectTransparency.types false in
private theorem written_error_testError (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .universalFirst))
    (accounting : NormalAccounting (starInstance P.tools .universalFirst)) (world : (P.input .universalFirst).World)
    {n : ℕ} {state : State (starInstance P.tools .universalFirst)}
    (path : Prefix (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
      (worldTapes (P.input .universalFirst) world) n state)
    (stage : (starInstance P.tools .universalFirst).Stage) (target : ℝ)
    (wrong : state.ledger.written stage = some (!state.ledger.truth stage))
    (targetAtWrite : ∀ (clock : ℕ) (old : State (starInstance P.tools .universalFirst)),
      Prefix (P.input .universalFirst) C .uncapped accounting (P.starReferenceRule .universalFirst .current r none)
        () ((P.input .universalFirst).truthAt world) (worldTapes (P.input .universalFirst) world) clock old →
      liveStage old stage → old.ledger.written stage = none →
      P.starReferenceRule .universalFirst .current r none () old.history = .write stage (!state.ledger.truth stage) →
      P.chosenTargetReal .universalFirst .current r old.history stage = some target) :
    (P.channel.symmetricHittingTest (realTargetIndex P.channel target)).rule.decision ()
      ((P.input .universalFirst).reviewAt world stage) ≠ (P.input .universalFirst).truthAt world stage := by
  obtain ⟨clock, old, _before, oldPath, active, write⟩ := prefix_written_has_write (P.input .universalFirst) C .uncapped accounting
    (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
    (worldTapes (P.input .universalFirst) world) path stage (!state.ledger.truth stage) wrong
  have legal := current_legal_uncapped P .universalFirst r none C accounting (Seed := Unit)
  obtain ⟨next, step⟩ := legal () _ _ clock old oldPath active
  rw [write] at step
  have live : liveStage old stage := by cases step with | write _ _ live _ _ => exact live
  have port : old.ledger.written stage = none := by cases step with | write _ _ _ port _ => exact port
  have chosen := targetAtWrite clock old oldPath live port write
  have decision := prefix_write_test_decision P .universalFirst .current r C accounting
    ((P.input .universalFirst).truthAt world) (worldTapes (P.input .universalFirst) world) oldPath
    stage (!state.ledger.truth stage) live port write target chosen
  have truths := prefix_truth (P.input .universalFirst) C .uncapped accounting
    (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
    (worldTapes (P.input .universalFirst) world) path
  rw [truths] at decision
  change (!(P.input .universalFirst).truthAt world stage) =
    (P.channel.symmetricHittingTest (realTargetIndex P.channel target)).rule.decision ()
      ((P.input .universalFirst).reviewAt world stage) at decision
  intro correct
  rw [correct] at decision
  cases actual : (P.input .universalFirst).truthAt world stage <;> simp [actual] at decision

set_option backward.isDefEq.respectTransparency.types false in
theorem universal_two_errors_testErrors (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .universalFirst)) (early : C.reporting = .early)
    (accounting : NormalAccounting (starInstance P.tools .universalFirst)) (world : (P.input .universalFirst).World)
    {n : ℕ} {state : State (starInstance P.tools .universalFirst)}
    (path : Prefix (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
      (worldTapes (P.input .universalFirst) world) n state)
    (headWrong : state.ledger.written (universalStage P.tools .universalFirst) =
      some (!state.ledger.truth (universalStage P.tools .universalFirst)))
    (secondWrong : state.ledger.written (singletonStage P.tools .universalFirst P.firstTool) =
      some (!state.ledger.truth (singletonStage P.tools .universalFirst P.firstTool))) :
    (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1))).rule.decision ()
      ((P.input .universalFirst).reviewAt world (universalStage P.tools .universalFirst)) ≠
        (P.input .universalFirst).truthAt world (universalStage P.tools .universalFirst) ∧
    (P.channel.symmetricHittingTest (realTargetIndex P.channel (min (1/4) (r / starTargetReal r 1)))).rule.decision ()
      ((P.input .universalFirst).reviewAt world (singletonStage P.tools .universalFirst P.firstTool)) ≠
        (P.input .universalFirst).truthAt world (singletonStage P.tools .universalFirst P.firstTool) := by
  constructor
  · apply written_error_testError P r C accounting world path _ _ headWrong
    intro clock old _path _live _port _write
    simp only [Parameters.chosenTargetReal, stageLabel_universal]
  · apply written_error_testError P r C accounting world path _ _ secondWrong
    intro clock old oldPath live _port _write
    have legal := current_legal_uncapped P .universalFirst r none C accounting (Seed := Unit)
    have before : (universalStage P.tools .universalFirst).val <
        (singletonStage P.tools .universalFirst P.firstTool).val := by change (0 : ℕ) < 0+1; decide
    have headWritten := prefix_pastWritten (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
      (worldTapes (P.input .universalFirst) world) oldPath (universalStage P.tools .universalFirst)
      (by rwa [live.2])
    obtain ⟨bit, written⟩ := Option.ne_none_iff_exists'.mp headWritten
    have sameBit := prefix_written_agree (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) legal () ((P.input .universalFirst).truthAt world)
      (worldTapes (P.input .universalFirst) world) oldPath path (universalStage P.tools .universalFirst)
      bit _ written headWrong
    have oldTruth := prefix_truth (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
      (worldTapes (P.input .universalFirst) world) oldPath
    have endTruth := prefix_truth (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
      (worldTapes (P.input .universalFirst) world) path
    have oldWrong : old.ledger.written (universalStage P.tools .universalFirst) =
        some (!old.ledger.truth (universalStage P.tools .universalFirst)) := by
      rw [sameBit, endTruth] at written
      rw [oldTruth]
      exact written
    have reportedWrong := (prefix_reportedError_iff_wrong (P.input .universalFirst) C early .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
      (worldTapes (P.input .universalFirst) world) oldPath (universalStage P.tools .universalFirst) headWritten).mpr oldWrong
    simp [Parameters.chosenTargetReal, stageLabel_singleton, Parameters.firstTool, reportedWrong]

end PaperProofs.Star.PStarUniversalTestErrors026
