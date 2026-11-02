module

public import PaperProofs.Star.PStar_PastTestErrors_030

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCountReviewBound031

open Common Common.Native Parameters PStarLR PStarActualHalt022 PStarTargetGates013
  PStarCountProbability019 PStarPastTestErrors030

def pastTestErrorGate (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (world : (P.input order).World) (stage : (starInstance P.tools order).Stage) : Prop :=
  ∀ earlier : (starInstance P.tools order).Stage, earlier.val < stage.val →
    (P.channel.symmetricHittingTest (realTargetIndex P.channel (stageTarget P r earlier.val))).rule.decision ()
      ((P.input order).reviewAt world earlier) ≠ (P.input order).truthAt world earlier

noncomputable def countReviewAllowance (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (world : (P.input order).World) (stage : (starInstance P.tools order).Stage) : ℕ∞ := by
  classical
  exact if pastTestErrorGate P order r world stage then
    realPosteriorStop P.channel.experiment (stageTarget P r stage.val) ((P.input order).reviewAt world stage) else 0

/-- Every actually charged review in the original count script occurs only
when all past ORIGINAL local tests err, and stays before the exact fixed
current-stage first exit. The bound retains all failed/nonreturn prefixes. -/
theorem prefix_countReviews_le (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (countKind : kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst))
    (r : ℝ) (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (world : (P.input order).World)
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none)
      () ((P.input order).truthAt world) (worldTapes (P.input order) world) n state) :
    ∀ stage : (starInstance P.tools order).Stage,
      state.ledger.reviews stage ≤ countReviewAllowance P order r world stage := by
  classical
  have early : C.reporting = .early := by
    cases kind with
    | current => exact qualified.1
    | earlyRetained => exact qualified.1
    | lateRetained => rcases countKind with impossible | ⟨impossible, _⟩ <;> cases impossible
  induction path with
  | initial => intro stage; exact zero_le
  | @next n state next earlier step ih =>
    generalize selected : P.starReferenceRule order kind r none () state.history = action at step
    cases step with
    | review stage live port resources =>
      intro other
      by_cases same : other = stage
      · subst other
        simp only [record, reviewLedger, Function.update_self]
        have sourceEq : run (P.input order) C .uncapped accounting
            (P.starReferenceRule order kind r none) ((),world) n = state := by
          have reconstructed : replayWorld (P.input order) ((P.input order).truthAt world)
              (worldTapes (P.input order) world) = world := rfl
          simpa only [reconstructed] using prefix_eq_run (P.input order) C .uncapped accounting
            (P.starReferenceRule order kind r none) () ((P.input order).truthAt world)
            (worldTapes (P.input order) world) earlier
        obtain ⟨target, chosen, before⟩ := PDROC.StarFirstExit.Local.review_current_before_stop
          P order kind r C accounting ((),world) n stage
          (by rw [sourceEq]; exact live) (by rw [sourceEq]; exact port) (by rw [sourceEq]; exact selected)
        rw [sourceEq] at chosen before
        have targetOnPrefix := countChosenTarget_on_prefix P order kind countKind r none C early .uncapped accounting
          () ((P.input order).truthAt world) (worldTapes (P.input order) world) earlier stage live.2
        rw [targetOnPrefix] at chosen
        by_cases pastWrong : ∀ previous : (starInstance P.tools order).Stage, previous.val < stage.val →
            state.ledger.written previous = some (!state.ledger.truth previous)
        · rw [ite_eq_left pastWrong] at chosen
          have targetEq : stageTarget P r stage.val = target := Option.some.inj chosen
          have offlineGate : pastTestErrorGate P order r world stage :=
            count_past_errors_testErrors P order kind countKind r C qualified accounting world earlier stage.val pastWrong
          rw [countReviewAllowance, ite_eq_left offlineGate]
          rw [← targetEq] at before
          exact (ENat.add_one_le_iff (prefix_reviews_finite (P.input order) C .uncapped accounting
            (P.starReferenceRule order kind r none) () _ _ earlier stage)).mpr before
        · rw [ite_eq_right pastWrong] at chosen
          cases chosen
      · change Function.update state.ledger.reviews stage (state.ledger.reviews stage+1) other ≤ _
        rw [Function.update_of_ne same]
        exact ih other
    | write => simp only [record, reportedWriteLedger]; split_ifs; exact ih
    | allocate | execute | advance | stop | abandon => exact ih

theorem run_countReviews_le (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (countKind : kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst))
    (r : ℝ) (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (sample : Unit × (P.input order).World)
    (n : ℕ) (stage : (starInstance P.tools order).Stage) :
    (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).ledger.reviews stage ≤
      countReviewAllowance P order r sample.2 stage := by
  rcases sample with ⟨⟨⟩,world⟩
  obtain ⟨clock, _bound, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) (reference_legal P order kind r C qualified accounting) ((),world) n
  exact prefix_countReviews_le P order kind countKind r C qualified accounting world path stage

end PaperProofs.Star.PStarCountReviewBound031
