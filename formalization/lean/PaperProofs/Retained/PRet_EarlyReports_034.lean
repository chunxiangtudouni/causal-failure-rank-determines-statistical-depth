module

public import PaperProofs.Common.NativeProtocol

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEarlyReports034

open Common Common.Native

variable {I : Instance}

/-- An early-report contract genuinely reports every ordinary written
stage on every actual Prefix, independent of eventual success. -/
theorem prefix_written_reported {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    ∀ stage, s.ledger.written stage ≠ none → ∃ clock, s.ledger.reportTime stage = some clock := by
  induction hp with
  | initial => intro stage h; exact False.elim (h rfl)
  | @next n s s' earlier step ih =>
    generalize haction : rule seed s.history = action at step
    cases step with
    | write current bit live port resources =>
      intro stage hwrite
      by_cases heq : stage = current
      · subst stage
        exact ⟨s.clock, by simp [record, reportedWriteLedger, hearly]⟩
      · have hw : s.ledger.written stage ≠ none := by
          simpa only [record, reportedWriteLedger, hearly, ↓reduceIte, writeLedger,
            Function.update_of_ne heq] using hwrite
        obtain ⟨clock, hc⟩ := ih stage hw
        exact ⟨clock, by simpa only [record, reportedWriteLedger, hearly, ↓reduceIte,
          writeLedger, Function.update_of_ne heq] using hc⟩
    | review | allocate | execute | advance | stop | abandon => exact ih

end PaperProofs.Retained.PRetEarlyReports034
