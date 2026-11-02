module

public import PaperProofs.Retained.PRet_FreshHeadPolicy_079

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshHeadRun080

open Common Common.Native PRetFreshHeadPolicy079

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- Every finite head-test prefix, also on infinite-test paths, is a real
prefix of the retained-aware full fresh interpreter. -/
theorem run_before (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (after : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hbound : (n : ℕ∞) ≤ test.rule.stop sample.1 (worldTapes input sample.2 head)) :
    run input (freshContract I) .uncapped (zeroNormalAccounting I) (rule input head test after) sample n =
      headReviewState input (zeroNormalAccounting I) head (input.truthAt sample.2) (worldTapes input sample.2 head) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnsucc : (n : ℕ∞) ≤ (n + 1 : ℕ∞) := by exact_mod_cast Nat.le_succ n
    have hr := ih (hnsucc.trans hbound)
    have hbefore : (n : ℕ∞) < test.rule.stop sample.1 (worldTapes input sample.2 head) :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hbound
    let s := headReviewState input (zeroNormalAccounting I) head (input.truthAt sample.2) (worldTapes input sample.2 head) n
    have ha : s.halted = false := headReviewState_active input (zeroNormalAccounting I) head _ _ n
    have hl : liveStage s head := ⟨ha, (headReviewState_cursor input (zeroNormalAccounting I) head _ _ n).trans hhead.symm⟩
    have hw : s.ledger.written head = none := congrFun (headReviewState_written input (zeroNormalAccounting I) head _ _ n) head
    have hc : s.ledger.reviews head = n := headReviewState_reviews input (zeroNormalAccounting I) head _ _ n
    have hcursor : s.cursor = 0 := headReviewState_cursor input (zeroNormalAccounting I) head _ _ n
    have hs : Step input (freshContract I) .uncapped (zeroNormalAccounting I) (worldTapes input sample.2) s (.review head)
        (headReviewState input (zeroNormalAccounting I) head (input.truthAt sample.2) (worldTapes input sample.2 head) (n + 1)) := by
      have h := Step.review (input := input) (C := freshContract I) (mode := .uncapped)
        (accounting := zeroNormalAccounting I) (tapes := worldTapes input sample.2) s head hl hw (.inl rfl)
      rw [headReviewState]
      simpa only [hc, ENat.toNat_natCast, hcursor] using h
    apply run_succ_of_step input (freshContract I) .uncapped (zeroNormalAccounting I) _ sample n _
    · rw [hr]
      exact ha
    · rw [hr, headReviewState_history, rule_headReviewHistory input head hhead,
        bellmanHeadNext_review input head test sample.1 _ n hbefore]
      exact hs

theorem run_write_at (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (after : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n) :
    run input (freshContract I) .uncapped (zeroNormalAccounting I) (rule input head test after) sample (n + 1) =
      let s := headReviewState input (zeroNormalAccounting I) head (input.truthAt sample.2) (worldTapes input sample.2 head) n
      record (zeroNormalAccounting I) s (.write head (test.rule.decision sample.1 (worldTapes input sample.2 head)))
        (writeResponses (freshContract I) s head (test.rule.decision sample.1 (worldTapes input sample.2 head)))
        (reportedWriteLedger (freshContract I) s head (test.rule.decision sample.1 (worldTapes input sample.2 head))) s.cursor false := by
  let s := headReviewState input (zeroNormalAccounting I) head (input.truthAt sample.2) (worldTapes input sample.2 head) n
  have hr := run_before input head hhead test after sample n (le_of_eq hstop.symm)
  have ha : s.halted = false := headReviewState_active input (zeroNormalAccounting I) head _ _ n
  have hl : liveStage s head := ⟨ha, (headReviewState_cursor input (zeroNormalAccounting I) head _ _ n).trans hhead.symm⟩
  have hw : s.ledger.written head = none := congrFun (headReviewState_written input (zeroNormalAccounting I) head _ _ n) head
  apply run_succ_of_step input (freshContract I) .uncapped (zeroNormalAccounting I) _ sample n _
  · rw [hr]
    exact ha
  · rw [hr, headReviewState_history, rule_headReviewHistory input head hhead,
      bellmanHeadNext_write input head test sample.1 _ n hstop]
    exact Step.write s head _ hl hw (.inl rfl)

end PaperProofs.Retained.PRetFreshHeadRun080
