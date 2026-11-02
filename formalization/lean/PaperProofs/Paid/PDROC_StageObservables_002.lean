module

public import PaperProofs.Paid.PDROC_StageObservables_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

theorem actualOrdinaryDecision_of_halted_unwritten (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*} [MeasurableSpace Seed]
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) (clock : ℕ) (stage : P.sharedInstance.Stage)
    (hh : (run (P.input fee hfee) C.val mode accounting rule sample clock).halted = true)
    (hw : (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.written stage = none) :
    P.actualOrdinaryDecision fee hfee C mode accounting rule sample stage = none := by
  classical
  have hnot (bit : Bool) : ¬ ∃ n, (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.written stage = some bit := by
    rintro ⟨n, hn⟩
    have h := run_written_some_after (P.input fee hfee) C.val mode accounting rule hl sample n clock stage bit hn
    rw [Nat.add_comm n clock, run_after_halt (P.input fee hfee) C.val mode accounting rule sample clock hh n, hw] at h
    cases h
  simp only [PaperProofs.Paid.Parameters.actualOrdinaryDecision, hnot true, hnot false, ↓reduceIte]

theorem paidRunReviewCount_of_halted (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*} [MeasurableSpace Seed]
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) (clock : ℕ) (stage : P.sharedInstance.Stage)
    (hh : (run (P.input fee hfee) C.val mode accounting rule sample clock).halted = true) :
    P.paidRunReviewCount fee hfee C mode accounting rule sample stage =
      (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.reviews stage := by
  apply le_antisymm
  · apply iSup_le
    intro n
    by_cases hn : n ≤ clock
    · exact run_reviews_mono (P.input fee hfee) C.val mode accounting rule hl sample stage hn
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hn)
      rw [run_after_halt (P.input fee hfee) C.val mode accounting rule sample clock hh extra]
  · exact le_iSup (fun n => (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.reviews stage) clock

theorem actualStageObservables_of_halted_unwritten (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*} [MeasurableSpace Seed]
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) (clock : ℕ) (stage : P.sharedInstance.Stage) (count : ℕ∞)
    (hh : (run (P.input fee hfee) C.val mode accounting rule sample clock).halted = true)
    (hw : (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.written stage = none)
    (hc : (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.reviews stage = count) :
    P.actualOrdinaryDecision fee hfee C mode accounting rule sample stage = none ∧
      P.paidRunReviewCount fee hfee C mode accounting rule sample stage = count :=
  ⟨actualOrdinaryDecision_of_halted_unwritten P fee hfee C mode accounting rule hl sample clock stage hh hw,
    (paidRunReviewCount_of_halted P fee hfee C mode accounting rule hl sample clock stage hh).trans hc⟩

end PDROC
