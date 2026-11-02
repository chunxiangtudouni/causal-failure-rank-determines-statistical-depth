module

public import PaperProofs.Paid.PDMenu_CurrentHeadKernel_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native

variable {I : Instance}

/-- Port of the original head-test realization to the current-payment guard.
The local test, observation tapes and actual interpreter are unchanged. -/
theorem paidHeadThenRule_headReviewHistory {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (after : PolicyRule I Seed) (seed : Seed) (tape : (input.experiment head).Tape) (n : ℕ) :
    paidHeadThenRule input head test available after seed (headReviewHistory input head tape n) =
      bellmanHeadNext input head test seed (headReviewHistory input head tape n) := by
  have hc := historyCursor_headReviewHistory input head tape n
  have hw := historyWritten_headReviewHistory input head tape n
  simp only [paidHeadThenRule, paidGuardedRule, bellmanHeadThenRaw, hw, ite_true]
  apply ite_eq_left
  unfold bellmanHeadNext
  dsimp only
  split_ifs <;> exact ⟨⟨hc.trans hhead.symm, hw⟩, True.intro⟩

theorem paidHeadThen_run_before {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (head : I.Stage) (hhead : head.val = 0) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (after : PolicyRule I Seed) (sample : Seed × input.World) (n : ℕ)
    (hbound : (n : ℕ∞) ≤ test.rule.stop sample.1 (worldTapes input sample.2 head)) :
    run input C .uncapped accounting (paidHeadThenRule input head test available after) sample n =
      headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnsucc : (n : ℕ∞) ≤ (n + 1 : ℕ∞) := by exact_mod_cast Nat.le_succ n
    have hn := hnsucc.trans hbound
    have hr := ih hn
    have hbefore : (n : ℕ∞) < test.rule.stop sample.1 (worldTapes input sample.2 head) :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hbound
    let s := headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n
    have ha : s.halted = false := headReviewState_active input accounting head _ _ n
    have hl : liveStage s head := ⟨ha, (headReviewState_cursor input accounting head _ _ n).trans hhead.symm⟩
    have hw : s.ledger.written head = none := congrFun (headReviewState_written input accounting head _ _ n) head
    have hc : s.ledger.reviews head = n := headReviewState_reviews input accounting head _ _ n
    have hcursor : s.cursor = 0 := headReviewState_cursor input accounting head _ _ n
    have hs : Step input C .uncapped accounting (worldTapes input sample.2) s (.review head)
        (headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) (n + 1)) := by
      have h := Step.review (input := input) (C := C) (mode := .uncapped) (accounting := accounting)
        (tapes := worldTapes input sample.2) s head hl hw (.inl rfl)
      rw [headReviewState]
      simpa only [hc, ENat.toNat_natCast, hcursor] using h
    apply run_succ_of_step input C .uncapped accounting _ sample n _
    · rw [hr]
      exact ha
    · rw [hr, headReviewState_history, paidHeadThenRule_headReviewHistory input head hhead,
        bellmanHeadNext_review input head test sample.1 _ n hbefore]
      exact hs

theorem paidHeadThen_run_write {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (head : I.Stage) (hhead : head.val = 0) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (after : PolicyRule I Seed) (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n) :
    run input C .uncapped accounting (paidHeadThenRule input head test available after) sample (n + 1) =
      bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)) := by
  have hr := paidHeadThen_run_before input C accounting head hhead test available after sample n (by rw [hstop])
  let s := headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n
  have ha : s.halted = false := headReviewState_active input accounting head _ _ n
  have hl : liveStage s head := ⟨ha, (headReviewState_cursor input accounting head _ _ n).trans hhead.symm⟩
  have hw : s.ledger.written head = none := congrFun (headReviewState_written input accounting head _ _ n) head
  apply run_succ_of_step input C .uncapped accounting _ sample n _
  · rw [hr]
    exact ha
  · rw [hr, headReviewState_history, paidHeadThenRule_headReviewHistory input head hhead,
      bellmanHeadNext_write input head test sample.1 _ n hstop]
    exact Step.write s head _ hl hw (.inl rfl)


end PDMenu

