module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_006
public import PaperProofs.Paid.PDROC_CalibratedRuntime_007
public import PaperProofs.Paid.PDROC_CalibratedRuntime_008
public import PaperProofs.Paid.PDMenu_MenuTerminalRecords_116
public import PaperProofs.Paid.PDMenu_MenuAbandonRecords_117

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu
open scoped ENNReal

namespace PDROC.CalibratedRuntime

/-- Exact terminal record of the original calibrated interpreter from a
genuine physical first entry. All write and stage-tool information is kept. -/
def EntryRecords (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + n = P.certificate.stages) : Prop :=
  let start := run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock
  let summary := pathSummary P (calibratedFamily P) table n (P.tools - start.ledger.executions.length)
    (calibratedSuffixSeed P cursor n hfit sample.1)
    (menuSuffixWorld P P.certificate.stages P.tools cursor n hfit fee hfee sample.2)
  ∃ ended : ℕ, clock ≤ ended ∧
    (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample ended).halted = true ∧
    (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample ended).ledger.observationBill (P.input fee hfee).fees =
      start.ledger.observationBill (P.input fee hfee).fees + summary.observation ∧
    TraceLedgerMatch P cursor (historyUsed start.history) summary.trace start
      (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample ended) ∧
    (runSuccess (P.input fee hfee) C .uncapped accounting (menuRule P table) sample ↔ summary.failure = false)

theorem menuRule_terminal_stop (P : Parameters) (table : MenuTable)
    (seed : P.CalibratedMenuSeed) (history : List (VisibleEvent P.sharedInstance))
    (hh : historyHalted history = false) (hc : historyCursor history = P.certificate.stages) :
    menuRule P table seed history = .stop := by
  have hcandidate : P.calibratedMenuCandidate table seed history = .stop := by
    simp only [calibratedMenuCandidate, hh, Bool.false_eq_true, ite_false, hc, Nat.lt_irrefl, ↓reduceDIte, ite_true]
  unfold menuRule searchGuardRule
  rw [hcandidate]
  rfl

theorem menuRule_unwrittenFrame (P : Parameters) (table : MenuTable)
    (seed : P.CalibratedMenuSeed) (history : List (VisibleEvent P.sharedInstance))
    (stage : P.sharedInstance.Stage) (hh : historyHalted history = false)
    (hc : historyCursor history = stage.val) (hw : historyWrite history stage = none) :
    menuRule P table seed history =
      match (menuEntryAt table (P.certificate.stages - stage.val)
        (P.menuEntryTools P.certificate.stages P.tools history stage)).action with
      | .finish | .abandon => .abandon
      | .test level _ => P.calibratedTestingAction level seed history stage := by
  have hlt : historyCursor history < P.certificate.stages := by
    rw [hc]
    simpa [sharedInstance] using stage.isLt
  have hs : (⟨historyCursor history, by simpa [sharedInstance] using hlt⟩ : P.sharedInstance.Stage) = stage :=
    Fin.ext hc
  have hcandidate : P.calibratedMenuCandidate table seed history =
      match (menuEntryAt table (P.certificate.stages - stage.val)
        (P.menuEntryTools P.certificate.stages P.tools history stage)).action with
      | .finish | .abandon => .abandon
      | .test level _ => P.calibratedTestingAction level seed history stage := by
    simp only [calibratedMenuCandidate, hh, Bool.false_eq_true, ite_false, dite_eq_left hlt, hs, hw]
    rw [hc]
    with_unfolding_all rfl
  unfold menuRule searchGuardRule
  rw [hcandidate]
  apply ite_eq_left
  cases ha : (menuEntryAt table (P.certificate.stages - stage.val)
    (P.menuEntryTools P.certificate.stages P.tools history stage)).action with
  | finish => trivial
  | abandon => trivial
  | test level bad => exact calibratedTestingAction_allowed P level seed history stage hc hw

theorem entryRecords_zero (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World)
    (cursor clock : ℕ) (hfit : cursor + 0 = P.certificate.stages)
    (hentry : FirstEntryAt (P.input fee hfee) C .uncapped accounting
      (menuRule P table) cursor clock sample) :
    EntryRecords P table fee hfee C accounting sample cursor 0 clock hfit := by
  let input := P.input fee hfee
  let rule := menuRule P table
  have hlegal := menuRule_legal P table fee hfee C hearly accounting
  have hactive := (firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry).1
  have hc : (run input C .uncapped accounting rule sample clock).cursor = P.certificate.stages :=
    hentry.1.trans (by simpa only [Nat.add_zero] using hfit)
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  have hh : historyHalted (run input C .uncapped accounting rule sample clock).history = false :=
    (prefix_historyHalted input C .uncapped accounting rule sample.1 _ _ hp).trans hactive
  have hv : historyCursor (run input C .uncapped accounting rule sample clock).history = P.certificate.stages :=
    (prefix_historyCursor input C .uncapped accounting rule sample.1 _ _ hp).trans hc
  have haction := menuRule_terminal_stop P table sample.1 _ hh hv
  have hstop := menu_run_stop input C accounting rule hlegal sample clock hactive haction
  have hhalt : (run input C .uncapped accounting rule sample (clock + 1)).halted = true := by rw [hstop]; rfl
  obtain ⟨m, _, hpEnd⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (clock + 1)
  have hcEnd : (run input C .uncapped accounting rule sample (clock + 1)).cursor = P.certificate.stages := by rw [hstop]; exact hc
  have haEnd : (run input C .uncapped accounting rule sample (clock + 1)).ledger.abandoned = false := by rw [hstop]; rfl
  have hsuccess : runSuccess input C .uncapped accounting rule sample :=
    ⟨clock + 1, hhalt, menuPrefix_terminal_success P table fee hfee C hearly accounting sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hpEnd hcEnd hhalt haEnd⟩
  simp only [EntryRecords, pathSummary_zero, finishRecord]
  refine ⟨clock + 1, Nat.le_succ clock, hhalt, ?_, ?_, ?_⟩
  · rw [hstop]
    exact (add_zero _).symm
  · apply traceLedgerMatch_nil
    · intro stage hs
      have hlt : stage.val < P.certificate.stages := by simpa [sharedInstance] using stage.isLt
      omega
    · rw [hstop]
      rfl
  · exact ⟨fun _ => True.intro, fun _ => hsuccess⟩

/-- Immediate abandonment preserves every unwritten future port and every
past physical execution. This helper has no continuation/IH premise. -/
theorem entryRecords_of_immediate_abandon (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + n = P.certificate.stages)
    (hentry : FirstEntryAt (P.input fee hfee) C .uncapped accounting (menuRule P table) cursor clock sample)
    (haction : menuRule P table sample.1
      (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock).history = .abandon)
    (hsummary : pathSummary P (calibratedFamily P) table n
      (P.tools - (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length)
      (calibratedSuffixSeed P cursor n hfit sample.1)
      (menuSuffixWorld P P.certificate.stages P.tools cursor n hfit fee hfee sample.2) = abandonRecord) :
    EntryRecords P table fee hfee C accounting sample cursor n clock hfit := by
  let input := P.input fee hfee
  let rule := menuRule P table
  have hlegal := menuRule_legal P table fee hfee C hearly accounting
  obtain ⟨hactive, hfresh⟩ := firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry
  have habandon := menu_run_abandon input C accounting rule hlegal sample clock hactive haction
  have hhalt : (run input C .uncapped accounting rule sample (clock + 1)).halted = true := by rw [habandon]; rfl
  have hfailure : ¬runSuccess input C .uncapped accounting rule sample := by
    intro hs
    have hbad := ((menu_runSuccess_iff_of_halted input C .uncapped accounting rule sample (clock + 1) hhalt).mp hs).2.1
    rw [habandon] at hbad
    change true = false at hbad
    cases hbad
  unfold EntryRecords
  dsimp only
  rw [hsummary]
  refine ⟨clock + 1, Nat.le_succ clock, hhalt, ?_, ?_, ?_⟩
  · rw [habandon]
    exact (add_zero _).symm
  · apply traceLedgerMatch_nil
    · intro stage hs
      rw [habandon]
      exact (hfresh stage hs).1
    · rw [habandon]
      rfl
  · exact ⟨fun hs => (hfailure hs).elim, fun hfalse => Bool.noConfusion hfalse⟩

end PDROC.CalibratedRuntime
