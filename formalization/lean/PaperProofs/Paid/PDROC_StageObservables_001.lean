module

public import PaperProofs.Paid.RepresentationClaims
public import PaperProofs.Common.NativeHeadAccounting

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem run_written_some_unique (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (hl : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (n m : ℕ) (stage : I.Stage) (bit bit' : Bool)
    (hn : (run input C mode accounting rule sample n).ledger.written stage = some bit)
    (hm : (run input C mode accounting rule sample m).ledger.written stage = some bit') : bit = bit' := by
  have ha := run_written_some_after input C mode accounting rule hl sample n m stage bit hn
  have hb := run_written_some_after input C mode accounting rule hl sample m n stage bit' hm
  rw [Nat.add_comm m n] at hb
  exact Option.some.inj (ha.symm.trans hb)

theorem actualOrdinaryDecision_of_written (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*} [MeasurableSpace Seed]
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) (n : ℕ) (stage : P.sharedInstance.Stage) (bit : Bool)
    (hw : (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.written stage = some bit) :
    P.actualOrdinaryDecision fee hfee C mode accounting rule sample stage = some bit := by
  classical
  cases bit with
  | true => simp [PaperProofs.Paid.Parameters.actualOrdinaryDecision, show ∃ k,
      (run (P.input fee hfee) C.val mode accounting rule sample k).ledger.written stage = some true from ⟨n, hw⟩]
  | false =>
    have hnot : ¬ ∃ k, (run (P.input fee hfee) C.val mode accounting rule sample k).ledger.written stage = some true := by
      rintro ⟨k, hk⟩
      have h := run_written_some_unique (P.input fee hfee) C.val mode accounting rule hl sample n k stage false true hw hk
      cases h
    simp [PaperProofs.Paid.Parameters.actualOrdinaryDecision, hnot, show ∃ k,
      (run (P.input fee hfee) C.val mode accounting rule sample k).ledger.written stage = some false from ⟨n, hw⟩]

theorem paidRunReviewCount_of_written (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*} [MeasurableSpace Seed]
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) (n : ℕ) (stage : P.sharedInstance.Stage) (bit : Bool)
    (hw : (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.written stage = some bit) :
    P.paidRunReviewCount fee hfee C mode accounting rule sample stage =
      (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.reviews stage := by
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hk : k ≤ n
    · exact run_reviews_mono (P.input fee hfee) C.val mode accounting rule hl sample stage hk
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hk)
      rw [run_reviews_written_port (P.input fee hfee) C.val mode accounting rule hl sample n extra stage bit hw]
  · exact le_iSup (fun k => (run (P.input fee hfee) C.val mode accounting rule sample k).ledger.reviews stage) n

theorem actualStageObservables_of_written (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*} [MeasurableSpace Seed]
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) (clock : ℕ) (stage : P.sharedInstance.Stage)
    (bit : Bool) (count : ℕ∞)
    (hw : (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.written stage = some bit)
    (hc : (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.reviews stage = count) :
    P.actualOrdinaryDecision fee hfee C mode accounting rule sample stage = some bit ∧
      P.paidRunReviewCount fee hfee C mode accounting rule sample stage = count :=
  ⟨actualOrdinaryDecision_of_written P fee hfee C mode accounting rule hl sample clock stage bit hw,
    (paidRunReviewCount_of_written P fee hfee C mode accounting rule hl sample clock stage bit hw).trans hc⟩

end PDROC
