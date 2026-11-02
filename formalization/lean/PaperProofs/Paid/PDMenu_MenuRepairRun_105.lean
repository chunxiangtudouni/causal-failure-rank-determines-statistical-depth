module

public import PaperProofs.Paid.PDMenu_MenuRepairPhases_104
public import PaperProofs.Paid.PDMenu_MenuSnapshotPackets_085

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Real allocate, real execute, and real advance from a fresh wrong write.
The physical tool returned by the original find? is used in all three
actual interpreter clocks; the next entry is concluded from the same run. -/
theorem compiledMenu_run_repair_threeSteps (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (stage : (freshInstance N K).Stage) (clock : ℕ) (bit : Bool) (level : ℕ)
    (hactive : (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).halted = false)
    (hcursor : (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).cursor = stage.val)
    (hbit : (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.written stage = some bit)
    (hwrong : bit ≠ (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.truth stage)
    (hcell : (Parameters.menuEntryAt table (N - stage.val)
      (P.menuEntryTools N K
        (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).history stage)).action = .test level .repair)
    (hnoCurrent : ∀ commitment ∈ (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.commitments,
      commitment.handle.stage ≠ stage)
    (havailable : 0 < (Finset.univ \ historyUsed
      (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).history).card) :
    let start := run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock
    let handle : MismatchHandle (freshInstance N K) := ⟨stage, start.ledger.writeSerial stage⟩
    ∃ tool : (freshInstance N K).Tool,
      let allocated := record accounting start (.allocate handle tool) [.committed handle tool]
        (allocateLedger start handle tool) start.cursor false
      let executed := record accounting allocated (.execute handle tool) [.executed handle tool]
        (executeLedger allocated handle tool) allocated.cursor false
      let advanced := record accounting executed (.advance stage) [.advanced stage]
        (advanceLedger executed stage) (executed.cursor + 1) false
      run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample (clock + 1) = allocated ∧
      run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample (clock + 2) = executed ∧
      run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample (clock + 3) = advanced ∧
      FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
        (P.compiledMenuRule N K table) (stage.val + 1) (clock + 3) sample := by
  let input := P.freshInput N K fee hfee
  let rule := P.compiledMenuRule N K table
  let start := run input C .uncapped accounting rule sample clock
  let handle : MismatchHandle (freshInstance N K) := ⟨stage, start.ledger.writeSerial stage⟩
  have hlegal := P.compiledMenuRule_uncapped_legal N K table fee hfee C hearly accounting
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  have hnoexec := menuPrefix_no_current_execution input C accounting rule sample.1 (input.truthAt sample.2)
    (worldTapes input sample.2) hp stage hnoCurrent
  obtain ⟨tool, _, hallocate⟩ := compiledMenuRule_fresh_repair_allocates P N K table fee hfee C hearly accounting
    rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp sample.1 stage bit level
    hactive hcursor hbit hwrong hcell hnoCurrent havailable
  let allocated := record accounting start (.allocate handle tool) [.committed handle tool]
    (allocateLedger start handle tool) start.cursor false
  let executed := record accounting allocated (.execute handle tool) [.executed handle tool]
    (executeLedger allocated handle tool) allocated.cursor false
  let advanced := record accounting executed (.advance stage) [.advanced stage]
    (advanceLedger executed stage) (executed.cursor + 1) false
  have hallocAction : rule sample.1 start.history = .allocate handle tool := hallocate
  have halloc : run input C .uncapped accounting rule sample (clock + 1) = allocated :=
    menu_run_allocate input C accounting rule hlegal sample clock handle tool hactive hallocAction
  have ha1 : (run input C .uncapped accounting rule sample (clock + 1)).halted = false := by rw [halloc]; rfl
  have hc1 : (run input C .uncapped accounting rule sample (clock + 1)).cursor = stage.val := by rw [halloc]; exact hcursor
  have hw1 : (run input C .uncapped accounting rule sample (clock + 1)).ledger.written stage = some bit := by rw [halloc]; exact hbit
  have hb1 : bit ≠ (run input C .uncapped accounting rule sample (clock + 1)).ledger.truth stage := by rw [halloc]; exact hwrong
  have hk1 : P.menuEntryTools N K allocated.history stage = P.menuEntryTools N K start.history stage :=
    menuEntryTools_append_event_no_execution P N K start.history stage (.committed handle tool) rfl
  have he1 : (Parameters.menuEntryAt table (N - stage.val)
      (P.menuEntryTools N K (run input C .uncapped accounting rule sample (clock + 1)).history stage)).action = .test level .repair := by
    rw [halloc, hk1]
    exact hcell
  have hn1 : ∀ execution ∈ (run input C .uncapped accounting rule sample (clock + 1)).ledger.executions,
      execution.handle.stage ≠ stage := by
    rw [halloc]
    exact hnoexec
  let commitment : Commitment (freshInstance N K) := ⟨handle, tool, start.clock⟩
  have hcommit : commitment ∈ (run input C .uncapped accounting rule sample (clock + 1)).ledger.commitments := by
    rw [halloc]
    exact List.mem_append_right _ (List.mem_singleton_self commitment)
  have hp1 := run_prefix_of_active input C .uncapped accounting rule hlegal sample (clock + 1) ha1
  have hexecAction : rule sample.1 (run input C .uncapped accounting rule sample (clock + 1)).history = .execute handle tool :=
    compiledMenuRule_allocated_repair_executes P N K table fee hfee C hearly accounting rule sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp1 sample.1 stage bit level ha1 hc1 hw1 hb1 he1 commitment hcommit rfl hn1
  have hexec : run input C .uncapped accounting rule sample (clock + 2) = executed := by
    have hr := menu_run_execute input C accounting rule hlegal sample (clock + 1) handle tool ha1 hexecAction
    rw [halloc] at hr
    simpa only [Nat.add_assoc] using hr
  have ha2 : (run input C .uncapped accounting rule sample (clock + 2)).halted = false := by rw [hexec]; rfl
  have hc2 : (run input C .uncapped accounting rule sample (clock + 2)).cursor = stage.val := by rw [hexec]; exact hcursor
  have hw2 : (run input C .uncapped accounting rule sample (clock + 2)).ledger.written stage = some bit := by rw [hexec]; exact hbit
  have hb2 : bit ≠ (run input C .uncapped accounting rule sample (clock + 2)).ledger.truth stage := by rw [hexec]; exact hwrong
  have hk2 : P.menuEntryTools N K executed.history stage = P.menuEntryTools N K allocated.history stage :=
    menuEntryTools_append_current_execution P N K allocated.history stage handle tool rfl
  have he2 : (Parameters.menuEntryAt table (N - stage.val)
      (P.menuEntryTools N K (run input C .uncapped accounting rule sample (clock + 2)).history stage)).action = .test level .repair := by
    rw [hexec, hk2, hk1]
    exact hcell
  let execution : Execution (freshInstance N K) := ⟨handle, tool, allocated.clock⟩
  have hexecution : execution ∈ (run input C .uncapped accounting rule sample (clock + 2)).ledger.executions := by
    rw [hexec]
    exact List.mem_append_right _ (List.mem_singleton_self execution)
  have hp2 := run_prefix_of_active input C .uncapped accounting rule hlegal sample (clock + 2) ha2
  have hadvAction : rule sample.1 (run input C .uncapped accounting rule sample (clock + 2)).history = .advance stage :=
    compiledMenuRule_executed_repair_advances P N K table fee hfee C hearly accounting rule sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp2 sample.1 stage bit level ha2 hc2 hw2 hb2 he2 execution hexecution rfl
  have hadv : run input C .uncapped accounting rule sample (clock + 3) = advanced := by
    have hr := menu_run_advance input C accounting rule hlegal sample (clock + 2) stage ha2 hadvAction
    rw [hexec] at hr
    simpa only [Nat.add_assoc] using hr
  have hn : (run input C .uncapped accounting rule sample (clock + 2 + 1)).cursor = stage.val + 1 := by
    have hr : run input C .uncapped accounting rule sample (clock + 2 + 1) = advanced := by
      simpa only [Nat.add_assoc] using hadv
    rw [hr]
    exact congrArg (fun n : ℕ => n + 1) hcursor
  have hentry := menuFirstEntryAfterAdvance input C .uncapped accounting rule hlegal sample (clock + 2) stage.val hc2 hn
  exact ⟨tool, halloc, hexec, hadv, by simpa only [Nat.add_assoc] using hentry⟩

end PDMenu
