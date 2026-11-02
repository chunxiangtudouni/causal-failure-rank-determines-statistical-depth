module

public import PaperProofs.Common.NativeCausality

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetPastWritten015

open Common Common.Native

variable {I : Instance}

private theorem reportedWrite_written (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).written = Function.update s.ledger.written stage (some bit) := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

/-- Passing a stage required a real ordinary write. This is true on every
actual Prefix, including failure, abandon and unfinished paths. -/
theorem prefix_past_written {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting sourceRule seed truth tapes n s) :
    ∀ stage : I.Stage, stage.val < s.cursor → s.ledger.written stage ≠ none := by
  induction hp with
  | initial => intro stage hstage; exact (Nat.not_lt_zero _ hstage).elim
  | @next n s s' hp step ih =>
    generalize haction : sourceRule seed s.history = action at step
    cases step with
    | write current bit live port resources =>
      intro stage hstage
      change (reportedWriteLedger C s current bit).written stage ≠ none
      rw [reportedWrite_written]
      by_cases heq : stage = current
      · subst stage
        simp
      · rw [Function.update_of_ne heq]
        exact ih stage hstage
    | advance current live written resources =>
      intro stage hstage
      change s.ledger.written stage ≠ none
      by_cases heq : stage = current
      · subst stage
        exact written
      · have hval : stage.val ≠ current.val := by intro he; exact heq (Fin.ext he)
        apply ih stage
        change stage.val < s.cursor + 1 at hstage
        have hcur := live.2
        omega
    | review | allocate | execute | stop | abandon => exact ih

/-- If a source interval creates no new ordinary writes, it can advance at
most one stage. Future-stage freshness and genuine past writes prove this;
no hidden source-run oracle or performance hypothesis is assumed. -/
theorem cursor_le_succ_of_written_eq {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (base : State I) (hbase : CursorInvariant base)
    {n : ℕ} {next : State I} (hp : Prefix input C mode accounting sourceRule seed truth tapes n next)
    (hwritten : next.ledger.written = base.ledger.written) : next.cursor ≤ base.cursor + 1 := by
  by_contra hle
  have hnext := (prefix_cursorInvariant input C mode accounting sourceRule seed truth tapes hp).bound
  have hstage : base.cursor + 1 < I.stageCount := by omega
  let stage : I.Stage := ⟨base.cursor + 1, hstage⟩
  have hpast := prefix_past_written input C mode accounting sourceRule seed truth tapes hp stage (by
    change base.cursor + 1 < next.cursor
    omega)
  have hfuture := hbase.future_written stage (by change base.cursor < base.cursor + 1; omega)
  rw [hwritten, hfuture] at hpast
  exact hpast rfl

end PaperProofs.Retained.PRetPastWritten015
