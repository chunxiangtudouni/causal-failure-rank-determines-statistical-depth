module

public import PaperProofs.Paid.PDROC_CalibratedIdeal_002
public import PaperProofs.Paid.PDROC_CalibratedRuntime_007
public import PaperProofs.Paid.PDROC_CalibratedRuntime_008
public import PaperProofs.Paid.PDROC_MenuNativeAbort_002
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu PDROC.CalibratedRuntime

namespace PDROC.CalibratedIdeal

theorem menuWrittenFrom_other {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (stage other : I.Stage) (start : State I)
    (tape : (input.experiment stage).Tape) (reviews : ℕ) (bit : Bool) (hne : other ≠ stage) :
    (menuWrittenFrom input C accounting stage start tape reviews bit).ledger.written other =
      start.ledger.written other := by
  classical
  simp only [menuWrittenFrom, record, reportedWriteLedger]
  split_ifs <;>
    simpa only [writeLedger, Function.update_of_ne hne] using
      congrFun (menuReviewFrom_written input accounting stage start tape reviews) other

theorem executionPairs_repaired (P : Parameters) (accounting : NormalAccounting P.sharedInstance)
    (stage : P.sharedInstance.Stage) (start : State P.sharedInstance) (tool : Fin P.tools) :
    executionPairs P (menuRepairedFrom accounting stage start tool).ledger =
      executionPairs P start.ledger ++ [(stage.val, tool)] := by
  simp only [executionPairs, menuRepairedFrom, record, advanceLedger, executeLedger,
    allocateLedger, List.map_append, List.map_cons, List.map_nil]

theorem bool_ne_eq_not (bit truth : Bool) (h : bit ≠ truth) : bit = !truth := by
  cases bit <;> cases truth <;> simp_all

/-- The strengthened part of the original finite-entry induction: exact
visited writes and exact physical stage/tool list, starting at the genuine
entry's actual used-tool set. All clocks are original interpreter clocks. -/
def EntryTrace (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + n = P.certificate.stages) : Prop :=
  let start := run (P.input fee hfee) C.val .uncapped accounting
    (P.compiledMenuRule P.certificate.stages P.tools table) sample clock
  let record := pathSummary P (idealFamily P) table n (P.tools - start.ledger.executions.length)
    (menuSuffixSeed P.certificate.stages P.tools cursor n hfit sample.1)
    (menuSuffixWorld P P.certificate.stages P.tools cursor n hfit fee hfee sample.2)
  ∃ ended, clock ≤ ended ∧
    (run (P.input fee hfee) C.val .uncapped accounting
      (P.compiledMenuRule P.certificate.stages P.tools table) sample ended).halted = true ∧
    TraceLedgerMatch P cursor (historyUsed start.history) record.trace start
      (run (P.input fee hfee) C.val .uncapped accounting
        (P.compiledMenuRule P.certificate.stages P.tools table) sample ended)

section Entry

variable (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World)

theorem entryTrace_zero (cursor clock : ℕ) (hfit : cursor + 0 = P.certificate.stages)
    (hentry : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (P.compiledMenuRule P.certificate.stages P.tools table) cursor clock sample) :
    EntryTrace P table fee hfee C accounting sample cursor 0 clock hfit := by
  let input := P.input fee hfee
  let rule := P.compiledMenuRule P.certificate.stages P.tools table
  have legal := P.compiledMenuRule_uncapped_legal P.certificate.stages P.tools table fee hfee C.val C.property.1.1 accounting
  have active := (firstEntryAt_unborn input C.val .uncapped accounting rule legal sample cursor clock hentry).1
  have hc : (run input C.val .uncapped accounting rule sample clock).cursor = P.certificate.stages :=
    hentry.1.trans (by simpa only [Nat.add_zero] using hfit)
  have hp := run_prefix_of_active input C.val .uncapped accounting rule legal sample clock active
  have action : rule sample.1 (run input C.val .uncapped accounting rule sample clock).history = .stop :=
    compiledMenuRule_terminal_stop P P.certificate.stages P.tools table fee hfee C.val C.property.1.1 accounting
      rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp sample.1 active hc
  have stopped := menu_run_stop input C.val accounting rule legal sample clock active action
  unfold EntryTrace
  dsimp only
  refine ⟨clock + 1, Nat.le_succ clock, ?_, ?_⟩
  · rw [stopped]
    rfl
  · apply traceLedgerMatch_nil
    · intro stage hs
      have lt : stage.val < P.certificate.stages := by simpa [Parameters.sharedInstance] using stage.isLt
      omega
    · rw [stopped]
      rfl

theorem entryTrace_abandon (cursor n clock : ℕ)
    (hfit : cursor + (n + 1) = P.certificate.stages)
    (stage : P.sharedInstance.Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (P.compiledMenuRule P.certificate.stages P.tools table) cursor clock sample)
    (ha : (menuEntryAt table (n + 1)
      (P.tools - (run (P.input fee hfee) C.val .uncapped accounting
        (P.compiledMenuRule P.certificate.stages P.tools table) sample clock).ledger.executions.length)).action = .abandon ∨
      (menuEntryAt table (n + 1)
      (P.tools - (run (P.input fee hfee) C.val .uncapped accounting
        (P.compiledMenuRule P.certificate.stages P.tools table) sample clock).ledger.executions.length)).action = .finish) :
    EntryTrace P table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.input fee hfee
  let rule := P.compiledMenuRule P.certificate.stages P.tools table
  let start := run input C.val .uncapped accounting rule sample clock
  have legal := P.compiledMenuRule_uncapped_legal P.certificate.stages P.tools table fee hfee C.val C.property.1.1 accounting
  obtain ⟨active, fresh⟩ := firstEntryAt_unborn input C.val .uncapped accounting rule legal sample cursor clock hentry
  have hc : start.cursor = stage.val := hentry.1.trans hstage.symm
  have port : start.ledger.written stage = none := (fresh stage (by omega)).1
  have hp := run_prefix_of_active input C.val .uncapped accounting rule legal sample clock active
  have hk := menuPrefix_entryTools_eq_physical_sub P P.certificate.stages P.tools table fee hfee C.val accounting
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage hc port
  have row : P.certificate.stages - stage.val = n + 1 := by omega
  have action : rule sample.1 start.history = .abandon := by
    apply compiledMenuRule_entry_abandon P P.certificate.stages P.tools table fee hfee C.val C.property.1.1 accounting
      rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp sample.1 stage active hc port
    rw [row, hk]
    exact ha
  have aborted := menu_run_abandon input C.val accounting rule legal sample clock active action
  unfold EntryTrace
  dsimp only
  rw [pathSummary_abandon P (idealFamily P) table n _ _ _ ha]
  refine ⟨clock + 1, Nat.le_succ clock, ?_, ?_⟩
  · rw [aborted]
    rfl
  · apply traceLedgerMatch_nil
    · intro other hs
      rw [aborted]
      exact (fresh other hs).1
    · rw [aborted]
      rfl

end Entry
end PDROC.CalibratedIdeal
