module

public import PaperProofs.Paid.PDROC_Simulator_001
public import PaperProofs.Common.HistorySuffixRun

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

def entryReviewState (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (entry : State I) (tape : (input.experiment stage).Tape) : ℕ → State I
  | 0 => entry
  | n + 1 =>
      let s := entryReviewState input accounting stage entry tape n
      record accounting s (.review stage) [.observation stage (tape n).val]
        (reviewLedger s stage) entry.cursor false

theorem entryReviewState_cursor (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (entry : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (entryReviewState input accounting stage entry tape n).cursor = entry.cursor := by cases n <;> rfl

theorem entryReviewState_active (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (entry : State I) (tape : (input.experiment stage).Tape) (n : ℕ)
    (ha : entry.halted = false) :
    (entryReviewState input accounting stage entry tape n).halted = false := by cases n; exact ha; rfl

theorem entryReviewState_written (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (entry : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (entryReviewState input accounting stage entry tape n).ledger.written = entry.ledger.written := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem entryReviewState_reviews (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (entry : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (entryReviewState input accounting stage entry tape n).ledger.reviews stage =
      entry.ledger.reviews stage + n := by
  induction n with
  | zero => simp only [entryReviewState, Nat.cast_zero, add_zero]
  | succ n ih => simp only [entryReviewState, record, reviewLedger, Function.update_self,
      ih, Nat.cast_add, Nat.cast_one, add_assoc]

theorem entryReviewState_history (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (entry : State I) (tape : (input.experiment stage).Tape) (n : ℕ) :
    (entryReviewState input accounting stage entry tape n).history =
      entry.history ++ headReviewHistory input stage tape n := by
  induction n with
  | zero => simp only [entryReviewState, headReviewHistory, List.ofFn_zero, List.append_nil]
  | succ n ih => simp only [entryReviewState, record, ih, headReviewHistory_succ, List.append_assoc]

universe u
variable {Seed : Type u}

/-- The direct simulator's concrete prewrite test is aligned with the ORIGINAL
run from its actual entry; no suffix-test equality or external trace is assumed. -/
theorem run_eq_entryReviewState_before_directExit (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance)
    (accounting : NormalAccounting P.sharedInstance) (rule : PolicyRule P.sharedInstance Seed)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (ha : (run (P.input fee hfee) C .uncapped accounting rule sample start).halted = false)
    (hcursor : (run (P.input fee hfee) C .uncapped accounting rule sample start).cursor = stage.val)
    (hport : (run (P.input fee hfee) C .uncapped accounting rule sample start).ledger.written stage = none)
    (hzero : (run (P.input fee hfee) C .uncapped accounting rule sample start).ledger.reviews stage = 0)
    (n : ℕ)
    (hbound : (n : ℕ∞) ≤ headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P rule)
      (sample.1, (run (P.input fee hfee) C .uncapped accounting rule sample start).history)
        (worldTapes (P.input fee hfee) sample.2 stage)) :
    run (P.input fee hfee) C .uncapped accounting rule sample (start + n) =
      entryReviewState (P.input fee hfee) accounting stage
        (run (P.input fee hfee) C .uncapped accounting rule sample start)
          (worldTapes (P.input fee hfee) sample.2 stage) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : (n : ℕ∞) ≤ headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P rule)
        (sample.1, (run (P.input fee hfee) C .uncapped accounting rule sample start).history)
          (worldTapes (P.input fee hfee) sample.2 stage) :=
      (show (n : ℕ∞) ≤ (n + 1 : ℕ∞) by exact_mod_cast Nat.le_succ n).trans hbound
    have hr := ih hn
    have haction := headExitStop_prior_review (P.input fee hfee) stage (simulatorPrewriteRule P rule)
      (sample.1, (run (P.input fee hfee) C .uncapped accounting rule sample start).history)
      (worldTapes (P.input fee hfee) sample.2 stage) (n + 1) hbound n (Nat.lt_succ_self n)
    let s := entryReviewState (P.input fee hfee) accounting stage
      (run (P.input fee hfee) C .uncapped accounting rule sample start)
        (worldTapes (P.input fee hfee) sample.2 stage) n
    have hsActive : s.halted = false := entryReviewState_active _ _ _ _ _ n ha
    have hsCursor : s.cursor = stage.val := (entryReviewState_cursor _ _ _ _ _ n).trans hcursor
    have hsPort : s.ledger.written stage = none := by
      change (entryReviewState _ _ _ _ _ _).ledger.written stage = none
      rw [entryReviewState_written]
      exact hport
    have hsReviews : s.ledger.reviews stage = (n : ℕ∞) := by
      change (entryReviewState _ _ _ _ _ _).ledger.reviews stage = _
      rw [entryReviewState_reviews, hzero, zero_add]
    have hs : Step (P.input fee hfee) C .uncapped accounting (worldTapes (P.input fee hfee) sample.2)
        s (.review stage) (entryReviewState (P.input fee hfee) accounting stage
          (run (P.input fee hfee) C .uncapped accounting rule sample start)
            (worldTapes (P.input fee hfee) sample.2 stage) (n + 1)) := by
      have h := Step.review (input := P.input fee hfee) (C := C) (mode := .uncapped) (accounting := accounting)
        (tapes := worldTapes (P.input fee hfee) sample.2) s stage ⟨hsActive, hsCursor⟩ hsPort (Or.inl rfl)
      rw [entryReviewState]
      simpa only [hsReviews, ENat.toNat_natCast, hsCursor, hcursor] using h
    rw [Nat.add_succ]
    apply run_succ_of_step (P.input fee hfee) C .uncapped accounting rule sample (start + n) _
    · rw [hr]
      exact hsActive
    · rw [hr, entryReviewState_history]
      change rule sample.1 (_ ++ _) = .review stage at haction
      rw [haction]
      exact hs

theorem firstEntry_directReviewPrefix (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance)
    (accounting : NormalAccounting P.sharedInstance) (rule : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C .uncapped accounting rule)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (he : FirstEntryAt (P.input fee hfee) C .uncapped accounting rule stage.val start sample)
    (n : ℕ)
    (hbound : (n : ℕ∞) ≤ headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P rule)
      (sample.1, (run (P.input fee hfee) C .uncapped accounting rule sample start).history)
        (worldTapes (P.input fee hfee) sample.2 stage)) :
    (run (P.input fee hfee) C .uncapped accounting rule sample (start + n)).history =
      (run (P.input fee hfee) C .uncapped accounting rule sample start).history ++
        headReviewHistory (P.input fee hfee) stage (worldTapes (P.input fee hfee) sample.2 stage) n := by
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn (P.input fee hfee) C .uncapped accounting rule hl sample stage.val start he
  rw [run_eq_entryReviewState_before_directExit P fee hfee C accounting rule sample start stage
    ha he.1 (hunborn stage le_rfl).1 (hunborn stage le_rfl).2 n hbound]
  exact entryReviewState_history _ _ _ _ _ n

end PDROC
