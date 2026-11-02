module

public import PaperProofs.Paid.PDLower_Posterior_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
theorem actualOrdinaryDecision_none_of_no_entry (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hf) C.val mode accounting rule)
    (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage)
    (hnone : entryHistory (P.input fee hf) C.val mode accounting rule stage sample = none) :
    P.actualOrdinaryDecision fee hf C mode accounting rule sample stage = none := by
  classical
  have hnot (bit : Bool) : ¬ ∃ n, (run (P.input fee hf) C.val mode accounting rule sample n).ledger.written stage = some bit := by
    rintro ⟨n, hn⟩
    have hw := (run_cursorInvariant (P.input fee hf) C.val mode accounting rule hl sample n).future_written stage
      (run_cursor_lt_of_no_entry (P.input fee hf) C.val mode accounting rule hl sample stage hnone n)
    rw [hw] at hn
    cases hn
  simp only [Parameters.actualOrdinaryDecision, hnot true, hnot false, ↓reduceIte]

theorem directFiniteStage_filledDecision (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed)
    (sample : Seed × (P.input fee hf).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (he : FirstEntryAt (P.input fee hf) C.val .uncapped accounting source.rule stage.val start sample)
    (n : ℕ)
    (hstop : headExitStop (P.input fee hf) stage (PDROC.simulatorPrewriteRule P source.rule)
      (sample.1, (run (P.input fee hf) C.val .uncapped accounting source.rule sample start).history)
        (worldTapes (P.input fee hf) sample.2 stage) = (n : ℕ∞)) :
    P.filledOrdinaryDecision fee hf C .uncapped accounting source.rule sample stage =
      (PDROC.optionWriteBit (source.rule sample.1
        (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n)).history)).getD
          (P.experiment.posteriorRecordDecision ((), ⟨n, fun k => (sample.2 stage).2 k.val⟩)) := by
  have hcount : P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage = (n : ℕ∞) := by
    apply le_antisymm
    · apply iSup_le
      intro k
      by_cases hk : k ≤ start + n
      · exact (run_reviews_mono (P.input fee hf) C.val .uncapped accounting source.rule source.legal sample stage hk).trans
          (PDROC.firstEntry_direct_reviews_after_exit P fee hf C accounting source.rule source.legal sample start stage he n hstop 0).le
      · obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge hk)
        rw [heq]
        exact (PDROC.firstEntry_direct_reviews_after_exit P fee hf C accounting source.rule source.legal sample start stage he n hstop extra).le
    · have hh := PDROC.firstEntry_direct_reviews_after_exit P fee hf C accounting source.rule source.legal sample start stage he n hstop 0
      have hb := le_iSup (fun clock => (run (P.input fee hf) C.val .uncapped accounting source.rule sample clock).ledger.reviews stage) (start + n)
      simpa only [Nat.add_zero] using hh.symm ▸ hb
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn (P.input fee hf) C.val .uncapped accounting source.rule source.legal sample stage.val start he
  have hr := PDROC.run_eq_entryReviewState_before_directExit P fee hf C.val accounting source.rule sample start stage ha he.1
    (hunborn stage le_rfl).1 (hunborn stage le_rfl).2 n (by rw [hstop])
  have hactive : (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n)).halted = false := by
    rw [hr]
    exact PDROC.entryReviewState_active _ _ _ _ _ _ ha
  have hopen : (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n)).ledger.written stage = none := by
    rw [hr, PDROC.entryReviewState_written]
    exact (hunborn stage le_rfl).1
  rcases PDROC.firstEntry_direct_exit_action_cases P fee hf C accounting source.rule source.legal sample start stage he n hstop with
    ⟨bit, hwrite⟩ | hstopAction | habandonAction
  · obtain ⟨_, _, hp⟩ := run_has_prefix (P.input fee hf) C.val .uncapped accounting source.rule source.legal sample (start + n)
    obtain ⟨next, hs⟩ := source.legal sample.1 _ _ _ _ hp hactive
    have hsOriginal := hs
    rw [hwrite] at hs
    have hnext := run_succ_of_step (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n) next hactive hsOriginal
    have hw : (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n + 1)).ledger.written stage = some bit := by
      rw [hnext]
      cases hs with
      | write =>
        simp only [record, reportedWriteLedger]
        split_ifs <;> simp [writeLedger]
    have hd := PDROC.actualOrdinaryDecision_of_written P fee hf C .uncapped accounting source.rule source.legal sample
      (start + n + 1) stage bit hw
    simp only [Parameters.filledOrdinaryDecision, hd, hwrite, PDROC.optionWriteBit, Option.getD_some]
  · have hs := Step.stop (input := P.input fee hf) (C := C.val) (mode := ResourceMode.uncapped)
      (accounting := accounting) (tapes := worldTapes (P.input fee hf) sample.2) _ hactive
    have hs' : Step (P.input fee hf) C.val .uncapped accounting (worldTapes (P.input fee hf) sample.2)
        (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n))
        (source.rule sample.1 (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n)).history)
        (stopState (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n)) false) := by
      rw [hstopAction]
      exact hs
    have hnext := run_succ_of_step (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n) _ hactive hs'
    have hh : (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n + 1)).halted = true := by rw [hnext]; rfl
    have hw : (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n + 1)).ledger.written stage = none := by
      rw [hnext]
      exact hopen
    have hd := PDROC.actualOrdinaryDecision_of_halted_unwritten P fee hf C .uncapped accounting source.rule source.legal sample
      (start + n + 1) stage hh hw
    simp only [Parameters.filledOrdinaryDecision, hd, hcount, ENat.natCast_ne_top, ↓reduceIte,
      hstopAction, PDROC.optionWriteBit, Option.getD_none]
    exact congrArg (fun count : ℕ∞ => P.experiment.posteriorRecordDecision
      ((), ⟨count.toNat, fun k => (sample.2 stage).2 k.val⟩)) hcount
  · have hs := Step.abandon (input := P.input fee hf) (C := C.val) (mode := ResourceMode.uncapped)
      (accounting := accounting) (tapes := worldTapes (P.input fee hf) sample.2) _ hactive
    have hs' : Step (P.input fee hf) C.val .uncapped accounting (worldTapes (P.input fee hf) sample.2)
        (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n))
        (source.rule sample.1 (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n)).history)
        (stopState (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n)) true) := by
      rw [habandonAction]
      exact hs
    have hnext := run_succ_of_step (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n) _ hactive hs'
    have hh : (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n + 1)).halted = true := by rw [hnext]; rfl
    have hw : (run (P.input fee hf) C.val .uncapped accounting source.rule sample (start + n + 1)).ledger.written stage = none := by
      rw [hnext]
      exact hopen
    have hd := PDROC.actualOrdinaryDecision_of_halted_unwritten P fee hf C .uncapped accounting source.rule source.legal sample
      (start + n + 1) stage hh hw
    simp only [Parameters.filledOrdinaryDecision, hd, hcount, ENat.natCast_ne_top, ↓reduceIte,
      habandonAction, PDROC.optionWriteBit, Option.getD_none]
    exact congrArg (fun count : ℕ∞ => P.experiment.posteriorRecordDecision
      ((), ⟨count.toNat, fun k => (sample.2 stage).2 k.val⟩)) hcount

end PDLower
