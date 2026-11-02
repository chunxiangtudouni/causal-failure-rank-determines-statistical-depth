module

public import PaperProofs.Paid.PDROC_DirectEntry_002
public import PaperProofs.Paid.PDROC_Simulator_014

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- The first finite direct exit at an actual fresh source entry can only
write that port or terminate, under the original current-payment contract. -/
theorem firstEntry_direct_exit_action_cases (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (rule : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting rule)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (he : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting rule stage.val start sample)
    (n : ℕ)
    (hstop : headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P rule)
      (sample.1, (run (P.input fee hfee) C.val .uncapped accounting rule sample start).history)
        (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞)) :
    (∃ bit, rule sample.1 (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).history =
      .write stage bit) ∨
    rule sample.1 (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).history = .stop ∨
    rule sample.1 (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).history = .abandon := by
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn (P.input fee hfee) C.val .uncapped accounting rule hl
    sample stage.val start he
  have hr := run_eq_entryReviewState_before_directExit P fee hfee C.val accounting rule sample start stage
    ha he.1 (hunborn stage le_rfl).1 (hunborn stage le_rfl).2 n (by rw [hstop])
  have hactive : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).halted = false := by
    rw [hr]
    exact entryReviewState_active _ _ _ _ _ n ha
  have hcursor : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).cursor = stage.val := by
    rw [hr, entryReviewState_cursor]
    exact he.1
  have hport : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).ledger.written stage = none := by
    rw [hr, entryReviewState_written]
    exact (hunborn stage le_rfl).1
  have hnot : rule sample.1 (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).history ≠ .review stage := by
    rw [hr, entryReviewState_history]
    exact headExitStop_hits (P.input fee hfee) stage (simulatorPrewriteRule P rule)
      (sample.1, (run (P.input fee hfee) C.val .uncapped accounting rule sample start).history)
      (worldTapes (P.input fee hfee) sample.2 stage) n hstop
  rcases currentPayment_unwritten_action_cases (P.input fee hfee) C.val C.property .uncapped accounting
    rule hl sample (start + n) stage hactive hcursor hport with hreview | hwrite | hstop' | habandon
  · exact (hnot hreview).elim
  · exact Or.inl hwrite
  · exact Or.inr (Or.inl hstop')
  · exact Or.inr (Or.inr habandon)

/-- The concrete simulator draw at an actual source entry retains exactly
one of the original lawful write/stop/abandon actions. -/
theorem firstEntry_simulatorDrawAt_action_cases (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (rule : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting rule)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (he : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting rule stage.val start sample)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorDrawAt P fee hfee rule stage sample.1
      (run (P.input fee hfee) C.val .uncapped accounting rule sample start).history
        (worldTapes (P.input fee hfee) sample.2 stage) = some draw) :
    (∃ bit, draw.action = .write stage bit) ∨ draw.action = .stop ∨ draw.action = .abandon := by
  let stop := headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P rule)
    (sample.1, (run (P.input fee hfee) C.val .uncapped accounting rule sample start).history)
      (worldTapes (P.input fee hfee) sample.2 stage)
  by_cases ht : stop = ⊤
  · simp only [simulatorDrawAt, show headExitStop _ _ _ _ _ = ⊤ from ht,
      ↓reduceIte, reduceCtorEq] at hd
  · have hs : headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P rule)
        (sample.1, (run (P.input fee hfee) C.val .uncapped accounting rule sample start).history)
          (worldTapes (P.input fee hfee) sample.2 stage) = (stop.toNat : ℕ∞) :=
      (ENat.natCast_toNat_eq_self.mpr ht).symm
    have heq : draw.action = rule sample.1
        ((run (P.input fee hfee) C.val .uncapped accounting rule sample start).history ++
          headReviewHistory (P.input fee hfee) stage
            (worldTapes (P.input fee hfee) sample.2 stage) stop.toNat) := by
      simp only [simulatorDrawAt, show headExitStop _ _ _ _ _ ≠ ⊤ from ht, ↓reduceIte,
        Option.some.injEq] at hd
      exact congrArg SimulatorDraw.action hd.symm
    rw [heq, ← firstEntry_directReviewPrefix P fee hfee C.val accounting rule hl sample start stage he
      stop.toNat (by rw [hs])]
    exact firstEntry_direct_exit_action_cases P fee hfee C accounting rule hl sample start stage he stop.toNat hs

end PDROC
