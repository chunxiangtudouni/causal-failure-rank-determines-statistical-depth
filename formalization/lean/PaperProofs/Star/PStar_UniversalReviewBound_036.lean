module

public import PaperProofs.Star.PStar_UniversalHeadError_035
public import PaperProofs.Star.PStar_ActualHalt_022

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarUniversalReviewBound036

open Common Common.Native Parameters PStarLR PStarCurrentLegality006 PStarUniversalHeadError035

def universalHeadTestError (P : PaperProofs.Star.Parameters) (r : ℝ) (world : (P.input .universalFirst).World) : Prop :=
  (P.channel.symmetricHittingTest (realTargetIndex P.channel (starTargetReal r 1))).rule.decision ()
    ((P.input .universalFirst).reviewAt world (universalStage P.tools .universalFirst)) ≠
      (P.input .universalFirst).truthAt world (universalStage P.tools .universalFirst)

theorem critical_ne_universal (P : PaperProofs.Star.Parameters) :
    singletonStage P.tools .universalFirst P.firstTool ≠ universalStage P.tools .universalFirst := by
  intro equal
  have values := congrArg Fin.val equal
  change (0+1 : ℕ) = 0 at values
  omega

noncomputable def universalReviewAllowance (P : PaperProofs.Star.Parameters) (r : ℝ)
    (world : (P.input .universalFirst).World) (stage : (starInstance P.tools .universalFirst).Stage) : ℕ∞ := by
  classical
  exact if stage = universalStage P.tools .universalFirst then
    realPosteriorStop P.channel.experiment (starTargetReal r 1) ((P.input .universalFirst).reviewAt world stage)
  else if stage = singletonStage P.tools .universalFirst P.firstTool ∧ universalHeadTestError P r world then
    realPosteriorStop P.channel.experiment (min (1/4) (r / starTargetReal r 1)) ((P.input .universalFirst).reviewAt world stage)
  else 0

theorem prefix_universalReviews_le (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .universalFirst)) (accounting : NormalAccounting (starInstance P.tools .universalFirst))
    (world : (P.input .universalFirst).World) {n : ℕ} {state : State (starInstance P.tools .universalFirst)}
    (path : Prefix (P.input .universalFirst) C .uncapped accounting (P.starReferenceRule .universalFirst .current r none)
      () ((P.input .universalFirst).truthAt world) (worldTapes (P.input .universalFirst) world) n state) :
    ∀ stage : (starInstance P.tools .universalFirst).Stage,
      state.ledger.reviews stage ≤ universalReviewAllowance P r world stage := by
  classical
  induction path with
  | initial => intro stage; exact zero_le
  | @next n state next earlier step ih =>
    generalize selected : P.starReferenceRule .universalFirst .current r none () state.history = action at step
    cases step with
    | review stage live port resources =>
      intro other
      by_cases same : other = stage
      · subst other
        simp only [record, reviewLedger, Function.update_self]
        have sourceEq : run (P.input .universalFirst) C .uncapped accounting
            (P.starReferenceRule .universalFirst .current r none) ((),world) n = state := by
          have reconstructed : replayWorld (P.input .universalFirst) ((P.input .universalFirst).truthAt world)
              (worldTapes (P.input .universalFirst) world) = world := rfl
          simpa only [reconstructed] using prefix_eq_run (P.input .universalFirst) C .uncapped accounting
            (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
            (worldTapes (P.input .universalFirst) world) earlier
        obtain ⟨target, chosen, before⟩ := PDROC.StarFirstExit.Local.review_current_before_stop
          P .universalFirst .current r C accounting ((),world) n stage
          (by rw [sourceEq]; exact live) (by rw [sourceEq]; exact port) (by rw [sourceEq]; exact selected)
        rw [sourceEq] at chosen before
        have finite := prefix_reviews_finite (P.input .universalFirst) C .uncapped accounting
          (P.starReferenceRule .universalFirst .current r none) () _ _ earlier stage
        rcases chosenTarget_Universal_cases P r state.history stage target chosen with
          ⟨universal, targetEq⟩ | ⟨critical, reported, targetEq⟩
        · rw [universalReviewAllowance, ite_eq_left universal]
          rw [targetEq] at before
          exact (ENat.add_one_le_iff finite).mpr before
        · have headWrong := (prefix_reportedError_genuine (P.input .universalFirst) C .uncapped accounting
            (P.starReferenceRule .universalFirst .current r none) () ((P.input .universalFirst).truthAt world)
            (worldTapes (P.input .universalFirst) world) earlier (universalStage P.tools .universalFirst) reported).1
          have headError : universalHeadTestError P r world :=
            universal_written_error_testError P r C accounting world earlier headWrong
          have notUniversal : stage ≠ universalStage P.tools .universalFirst := by
            rw [critical]
            exact critical_ne_universal P
          rw [universalReviewAllowance, ite_eq_right notUniversal, ite_eq_left ⟨critical, headError⟩]
          rw [targetEq] at before
          exact (ENat.add_one_le_iff finite).mpr before
      · change Function.update state.ledger.reviews stage (state.ledger.reviews stage+1) other ≤ _
        rw [Function.update_of_ne same]
        exact ih other
    | write => simp only [record, reportedWriteLedger]; split_ifs <;> exact ih
    | allocate | execute | advance | stop | abandon => exact ih

theorem run_universalReviews_le (P : PaperProofs.Star.Parameters) (r : ℝ)
    (C : Contract (starInstance P.tools .universalFirst)) (accounting : NormalAccounting (starInstance P.tools .universalFirst))
    (sample : Unit × (P.input .universalFirst).World) (n : ℕ) (stage : (starInstance P.tools .universalFirst).Stage) :
    (run (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none) sample n).ledger.reviews stage ≤
      universalReviewAllowance P r sample.2 stage := by
  rcases sample with ⟨⟨⟩,world⟩
  obtain ⟨clock, _bound, path⟩ := run_has_prefix (P.input .universalFirst) C .uncapped accounting
    (P.starReferenceRule .universalFirst .current r none) (current_legal_uncapped P .universalFirst r none C accounting) ((),world) n
  exact prefix_universalReviews_le P r C accounting world path stage

end PaperProofs.Star.PStarUniversalReviewBound036
