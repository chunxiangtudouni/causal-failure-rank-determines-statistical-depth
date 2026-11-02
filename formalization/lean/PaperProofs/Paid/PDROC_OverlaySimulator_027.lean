module

public import PaperProofs.Paid.PDROC_OverlaySimulator_025
public import PaperProofs.Paid.PDROC_DirectEntry_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- Before an actual write, an active current-payment Native port can only
have accumulated its own reviews since its first entry. The proof keeps
nonreturn as infinity and imposes no finite-time or expected-cost premise. -/
theorem overlay_prewrite_history_eq_reviews (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting rule)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (he : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting rule stage.val start sample)
    (n : ℕ)
    (ha : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).halted = false)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).ledger.written stage = none) :
    (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).history =
      (run (P.input fee hfee) C.val .uncapped accounting rule sample start).history ++
        headReviewHistory (P.input fee hfee) stage (worldTapes (P.input fee hfee) sample.2 stage) n := by
  classical
  let input := P.input fee hfee
  let tape := worldTapes input sample.2 stage
  let entry := run input C.val .uncapped accounting rule sample start
  let stop := headExitStop input stage (simulatorPrewriteRule P rule) (sample.1, entry.history) tape
  obtain ⟨ha0, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting rule hl sample stage.val start he
  have hb : (n : ℕ∞) ≤ stop := by
    by_contra hn
    have hlt : stop < (n : ℕ∞) := lt_of_not_ge hn
    have hfinite : stop ≠ ⊤ := by
      intro ht
      rw [ht] at hlt
      exact (not_lt_of_ge (le_top : (n : ℕ∞) ≤ ⊤)) hlt
    lift stop to ℕ using hfinite with k hk
    have hkn : k < n := ENat.natCast_lt_natCast.mp hlt
    have hs : headExitStop input stage (simulatorPrewriteRule P rule) (sample.1, entry.history) tape = (k : ℕ∞) := hk.symm
    have hr := run_eq_entryReviewState_before_directExit P fee hfee C.val accounting rule sample start stage
      ha0 he.1 (hunborn stage le_rfl).1 (hunborn stage le_rfl).2 k (by rw [hs])
    let cur := run input C.val .uncapped accounting rule sample (start + k)
    have hactive : cur.halted = false := by
      rw [show cur = entryReviewState input accounting stage entry tape k from hr]
      exact entryReviewState_active input accounting stage entry tape k ha0
    have hcursor : cur.cursor = stage.val := by
      rw [show cur = entryReviewState input accounting stage entry tape k from hr, entryReviewState_cursor]
      exact he.1
    have hport : cur.ledger.written stage = none := by
      rw [show cur = entryReviewState input accounting stage entry tape k from hr, entryReviewState_written]
      exact (hunborn stage le_rfl).1
    obtain ⟨extra, hx⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hkn)
    have hclock : start + n = (start + k + 1) + extra := by omega
    rcases firstEntry_direct_exit_action_cases P fee hfee C accounting rule hl sample start stage he k hs with
      ⟨bit, hwrite⟩ | hstop | habandon
    · let next := record accounting cur (.write stage bit) (writeResponses C.val cur stage bit)
        (reportedWriteLedger C.val cur stage bit) cur.cursor false
      have hstep : Step input C.val .uncapped accounting (worldTapes input sample.2) cur (.write stage bit) next :=
        .write cur stage bit ⟨hactive, hcursor⟩ hport (Or.inl rfl)
      have hnext := run_succ_of_step input C.val .uncapped accounting rule sample (start + k) next hactive
        (by rw [hwrite]; exact hstep)
      have hbit : (run input C.val .uncapped accounting rule sample (start + k + 1)).ledger.written stage = some bit := by
        rw [hnext]
        simp only [next, record, reportedWriteLedger, C.property.1.1, ite_true, writeLedger, Function.update_self]
      have hpersist := run_written_some_after input C.val .uncapped accounting rule hl sample
        (start + k + 1) extra stage bit hbit
      rw [← hclock, hw] at hpersist
      cases hpersist
    · have hstep : Step input C.val .uncapped accounting (worldTapes input sample.2) cur
          (rule sample.1 cur.history) (stopState cur false) := by rw [hstop]; exact .stop cur hactive
      have hnext := run_succ_of_step input C.val .uncapped accounting rule sample (start + k) _ hactive hstep
      have hhalt : (run input C.val .uncapped accounting rule sample (start + k + 1)).halted = true := by rw [hnext]; rfl
      have hpersist := run_after_halt input C.val .uncapped accounting rule sample (start + k + 1) hhalt extra
      have heq : (run input C.val .uncapped accounting rule sample (start + n)).halted = true := by
        rw [hclock, hpersist]
        exact hhalt
      rw [ha] at heq
      cases heq
    · have hstep : Step input C.val .uncapped accounting (worldTapes input sample.2) cur
          (rule sample.1 cur.history) (stopState cur true) := by rw [habandon]; exact .abandon cur hactive
      have hnext := run_succ_of_step input C.val .uncapped accounting rule sample (start + k) _ hactive hstep
      have hhalt : (run input C.val .uncapped accounting rule sample (start + k + 1)).halted = true := by rw [hnext]; rfl
      have hpersist := run_after_halt input C.val .uncapped accounting rule sample (start + k + 1) hhalt extra
      have heq : (run input C.val .uncapped accounting rule sample (start + n)).halted = true := by
        rw [hclock, hpersist]
        exact hhalt
      rw [ha] at heq
      cases heq
  rw [run_eq_entryReviewState_before_directExit P fee hfee C.val accounting rule sample start stage
    ha0 he.1 (hunborn stage le_rfl).1 (hunborn stage le_rfl).2 n hb]
  exact entryReviewState_history input accounting stage entry tape n

end PDROC
