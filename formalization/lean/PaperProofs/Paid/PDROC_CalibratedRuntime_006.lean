module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_005
public import PaperProofs.Paid.PDMenu_MenuRepairRun_105
public import PaperProofs.Paid.PDMenu_MenuEmptyRepair_111
public import PaperProofs.Paid.PDMenu_MenuEntryBranches_112

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu

namespace PDROC.CalibratedRuntime

variable {Seed : Type*}

theorem menuRule_written_eq_original_on_prefix (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance)
    (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {clock : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : P.CalibratedMenuSeed) (stage : P.sharedInstance.Stage) (bit : Bool)
    (hcursor : state.cursor = stage.val) (hbit : state.ledger.written stage = some bit) :
    menuRule P table menuSeed state.history =
      P.compiledMenuRule P.certificate.stages P.tools table menuSeed.1 state.history := by
  have hc : historyCursor state.history = stage.val :=
    (prefix_historyCursor (P.input fee hfee) C .uncapped accounting rule seed truth tapes hp).trans hcursor
  have hw : historyWrite state.history stage = some (bit, state.ledger.writeSerial stage) := by
    rw [prefix_historyWrite (P.input fee hfee) C .uncapped accounting rule seed truth tapes hp stage, hbit]
    rfl
  exact menuRule_written_eq_original P table menuSeed state.history stage bit _ hc hw

theorem menuRule_fresh_repair_allocates (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) {Seed : Type*}
    (rule : PolicyRule (freshInstance P.certificate.stages P.tools) Seed) (seed : Seed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : P.CalibratedMenuSeed) (stage : (freshInstance P.certificate.stages P.tools).Stage) (bit : Bool) (level : ℕ)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) (hwrong : bit ≠ state.ledger.truth stage)
    (hcell : (Parameters.menuEntryAt table (P.certificate.stages - stage.val)
      (P.menuEntryTools P.certificate.stages P.tools state.history stage)).action = .test level .repair)
    (hnoCurrent : ∀ commitment ∈ state.ledger.commitments, commitment.handle.stage ≠ stage)
    (havailable : 0 < (Finset.univ \ historyUsed state.history).card) :
    ∃ tool, P.menuUnusedTool P.certificate.stages P.tools state.history = some tool ∧
      menuRule P table menuSeed state.history =
        .allocate ⟨stage, state.ledger.writeSerial stage⟩ tool  := by
  obtain ⟨tool, hfind, ha⟩ := PDMenu.compiledMenuRule_fresh_repair_allocates P P.certificate.stages P.tools table fee hfee C hearly accounting
    rule seed truth tapes hp menuSeed.1 stage bit level hactive hcursor hbit hwrong hcell hnoCurrent havailable
  refine ⟨tool, hfind, ?_⟩
  rw [menuRule_written_eq_original_on_prefix P table fee hfee C accounting rule seed truth tapes hp
    menuSeed stage bit hcursor hbit]
  exact ha


theorem menuRule_allocated_repair_executes (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools))
    (rule : PolicyRule (freshInstance P.certificate.stages P.tools) Seed) (seed : Seed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : P.CalibratedMenuSeed) (stage : (freshInstance P.certificate.stages P.tools).Stage) (bit : Bool) (level : ℕ)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) (hwrong : bit ≠ state.ledger.truth stage)
    (hcell : (Parameters.menuEntryAt table (P.certificate.stages - stage.val)
      (P.menuEntryTools P.certificate.stages P.tools state.history stage)).action = .test level .repair)
    (commitment : Commitment (freshInstance P.certificate.stages P.tools)) (hc : commitment ∈ state.ledger.commitments)
    (hs : commitment.handle.stage = stage)
    (hnoexec : ∀ execution ∈ state.ledger.executions, execution.handle.stage ≠ stage) :
    menuRule P table menuSeed state.history = .execute commitment.handle commitment.tool  := by
  rw [menuRule_written_eq_original_on_prefix P table fee hfee C accounting rule seed truth tapes hp
    menuSeed stage bit hcursor hbit]
  exact PDMenu.compiledMenuRule_allocated_repair_executes P P.certificate.stages P.tools table fee hfee C hearly accounting
    rule seed truth tapes hp menuSeed.1 stage bit level hactive hcursor hbit hwrong hcell commitment hc hs hnoexec


theorem menuRule_executed_repair_advances (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools))
    (rule : PolicyRule (freshInstance P.certificate.stages P.tools) Seed) (seed : Seed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : P.CalibratedMenuSeed) (stage : (freshInstance P.certificate.stages P.tools).Stage) (bit : Bool) (level : ℕ)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) (hwrong : bit ≠ state.ledger.truth stage)
    (hcell : (Parameters.menuEntryAt table (P.certificate.stages - stage.val)
      (P.menuEntryTools P.certificate.stages P.tools state.history stage)).action = .test level .repair)
    (execution : Execution (freshInstance P.certificate.stages P.tools)) (he : execution ∈ state.ledger.executions)
    (hs : execution.handle.stage = stage) :
    menuRule P table menuSeed state.history = .advance stage  := by
  rw [menuRule_written_eq_original_on_prefix P table fee hfee C accounting rule seed truth tapes hp
    menuSeed stage bit hcursor hbit]
  exact PDMenu.compiledMenuRule_executed_repair_advances P P.certificate.stages P.tools table fee hfee C hearly accounting
    rule seed truth tapes hp menuSeed.1 stage bit level hactive hcursor hbit hwrong hcell execution he hs


theorem menuRule_fresh_repair_no_tool (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) {Seed : Type*}
    (rule : PolicyRule (freshInstance P.certificate.stages P.tools) Seed) (seed : Seed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : P.CalibratedMenuSeed) (stage : (freshInstance P.certificate.stages P.tools).Stage) (bit : Bool) (level : ℕ)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) (hwrong : bit ≠ state.ledger.truth stage)
    (hcell : (Parameters.menuEntryAt table (P.certificate.stages - stage.val)
      (P.menuEntryTools P.certificate.stages P.tools state.history stage)).action = .test level .repair)
    (hnoCurrent : ∀ commitment ∈ state.ledger.commitments, commitment.handle.stage ≠ stage)
    (havailable : (Finset.univ \ historyUsed state.history).card = 0) :
    menuRule P table menuSeed state.history = .abandon  := by
  rw [menuRule_written_eq_original_on_prefix P table fee hfee C accounting rule seed truth tapes hp
    menuSeed stage bit hcursor hbit]
  exact PDMenu.compiledMenuRule_fresh_repair_no_tool P P.certificate.stages P.tools table fee hfee C hearly accounting
    rule seed truth tapes hp menuSeed.1 stage bit level hactive hcursor hbit hwrong hcell hnoCurrent havailable


theorem menu_run_repair_threeSteps (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools))
    (sample : P.CalibratedMenuSeed × (P.freshInput P.certificate.stages P.tools fee hfee).World)
    (stage : (freshInstance P.certificate.stages P.tools).Stage) (clock : ℕ) (bit : Bool) (level : ℕ)
    (hactive : (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).halted = false)
    (hcursor : (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).cursor = stage.val)
    (hbit : (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.written stage = some bit)
    (hwrong : bit ≠ (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.truth stage)
    (hcell : (Parameters.menuEntryAt table (P.certificate.stages - stage.val)
      (P.menuEntryTools P.certificate.stages P.tools
        (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).history stage)).action = .test level .repair)
    (hnoCurrent : ∀ commitment ∈ (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.commitments,
      commitment.handle.stage ≠ stage)
    (havailable : 0 < (Finset.univ \ historyUsed
      (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).history).card) :
    let start := run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock
    let handle : MismatchHandle (freshInstance P.certificate.stages P.tools) := ⟨stage, start.ledger.writeSerial stage⟩
    ∃ tool : (freshInstance P.certificate.stages P.tools).Tool,
      P.menuUnusedTool P.certificate.stages P.tools start.history = some tool ∧
      let allocated := record accounting start (.allocate handle tool) [.committed handle tool]
        (allocateLedger start handle tool) start.cursor false
      let executed := record accounting allocated (.execute handle tool) [.executed handle tool]
        (executeLedger allocated handle tool) allocated.cursor false
      let advanced := record accounting executed (.advance stage) [.advanced stage]
        (advanceLedger executed stage) (executed.cursor + 1) false
      run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample (clock + 1) = allocated ∧
      run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample (clock + 2) = executed ∧
      run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample (clock + 3) = advanced ∧
      FirstEntryAt (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
        (menuRule P table) (stage.val + 1) (clock + 3) sample := by
  let input := P.freshInput P.certificate.stages P.tools fee hfee
  let rule := menuRule P table
  let start := run input C .uncapped accounting rule sample clock
  let handle : MismatchHandle (freshInstance P.certificate.stages P.tools) := ⟨stage, start.ledger.writeSerial stage⟩
  have hlegal := menuRule_legal P table fee hfee C hearly accounting
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  have hnoexec := menuPrefix_no_current_execution input C accounting rule sample.1 (input.truthAt sample.2)
    (worldTapes input sample.2) hp stage hnoCurrent
  obtain ⟨tool, hfind, hallocate⟩ := menuRule_fresh_repair_allocates P table fee hfee C hearly accounting
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
  have hk1 : P.menuEntryTools P.certificate.stages P.tools allocated.history stage = P.menuEntryTools P.certificate.stages P.tools start.history stage :=
    menuEntryTools_append_event_no_execution P P.certificate.stages P.tools start.history stage (.committed handle tool) rfl
  have he1 : (Parameters.menuEntryAt table (P.certificate.stages - stage.val)
      (P.menuEntryTools P.certificate.stages P.tools (run input C .uncapped accounting rule sample (clock + 1)).history stage)).action = .test level .repair := by
    rw [halloc, hk1]
    exact hcell
  have hn1 : ∀ execution ∈ (run input C .uncapped accounting rule sample (clock + 1)).ledger.executions,
      execution.handle.stage ≠ stage := by
    rw [halloc]
    exact hnoexec
  let commitment : Commitment (freshInstance P.certificate.stages P.tools) := ⟨handle, tool, start.clock⟩
  have hcommit : commitment ∈ (run input C .uncapped accounting rule sample (clock + 1)).ledger.commitments := by
    rw [halloc]
    exact List.mem_append_right _ (List.mem_singleton_self commitment)
  have hp1 := run_prefix_of_active input C .uncapped accounting rule hlegal sample (clock + 1) ha1
  have hexecAction : rule sample.1 (run input C .uncapped accounting rule sample (clock + 1)).history = .execute handle tool :=
    menuRule_allocated_repair_executes P table fee hfee C hearly accounting rule sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp1 sample.1 stage bit level ha1 hc1 hw1 hb1 he1 commitment hcommit rfl hn1
  have hexec : run input C .uncapped accounting rule sample (clock + 2) = executed := by
    have hr := menu_run_execute input C accounting rule hlegal sample (clock + 1) handle tool ha1 hexecAction
    rw [halloc] at hr
    simpa only [Nat.add_assoc] using hr
  have ha2 : (run input C .uncapped accounting rule sample (clock + 2)).halted = false := by rw [hexec]; rfl
  have hc2 : (run input C .uncapped accounting rule sample (clock + 2)).cursor = stage.val := by rw [hexec]; exact hcursor
  have hw2 : (run input C .uncapped accounting rule sample (clock + 2)).ledger.written stage = some bit := by rw [hexec]; exact hbit
  have hb2 : bit ≠ (run input C .uncapped accounting rule sample (clock + 2)).ledger.truth stage := by rw [hexec]; exact hwrong
  have hk2 : P.menuEntryTools P.certificate.stages P.tools executed.history stage = P.menuEntryTools P.certificate.stages P.tools allocated.history stage :=
    menuEntryTools_append_current_execution P P.certificate.stages P.tools allocated.history stage handle tool rfl
  have he2 : (Parameters.menuEntryAt table (P.certificate.stages - stage.val)
      (P.menuEntryTools P.certificate.stages P.tools (run input C .uncapped accounting rule sample (clock + 2)).history stage)).action = .test level .repair := by
    rw [hexec, hk2, hk1]
    exact hcell
  let execution : Execution (freshInstance P.certificate.stages P.tools) := ⟨handle, tool, allocated.clock⟩
  have hexecution : execution ∈ (run input C .uncapped accounting rule sample (clock + 2)).ledger.executions := by
    rw [hexec]
    exact List.mem_append_right _ (List.mem_singleton_self execution)
  have hp2 := run_prefix_of_active input C .uncapped accounting rule hlegal sample (clock + 2) ha2
  have hadvAction : rule sample.1 (run input C .uncapped accounting rule sample (clock + 2)).history = .advance stage :=
    menuRule_executed_repair_advances P table fee hfee C hearly accounting rule sample.1
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
  exact ⟨tool, hfind, halloc, hexec, hadv, by simpa only [Nat.add_assoc] using hentry⟩


theorem menuRule_written_correct (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) {Seed : Type*}
    (rule : PolicyRule (freshInstance P.certificate.stages P.tools) Seed) (seed : Seed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : P.CalibratedMenuSeed) (stage : (freshInstance P.certificate.stages P.tools).Stage)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some (state.ledger.truth stage)) :
    menuRule P table menuSeed state.history = .advance stage := by
  rw [menuRule_writtenFrame P table fee hfee C hearly accounting rule seed truth tapes hp
    menuSeed stage (state.ledger.truth stage) hactive hcursor hbit]
  simp only [beq_self_eq_true, ite_true]


theorem menuRule_written_wrong (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) {Seed : Type*}
    (rule : PolicyRule (freshInstance P.certificate.stages P.tools) Seed) (seed : Seed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : P.CalibratedMenuSeed) (stage : (freshInstance P.certificate.stages P.tools).Stage) (bit : Bool)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) (hwrong : bit ≠ state.ledger.truth stage) :
    menuRule P table menuSeed state.history =
      match (Parameters.menuEntryAt table (P.certificate.stages - stage.val)
        (P.menuEntryTools P.certificate.stages P.tools state.history stage)).action with
      | .test _ .repair => P.menuRepairAction P.certificate.stages P.tools state.history stage
      | _ => .abandon := by
  rw [menuRule_writtenFrame P table fee hfee C hearly accounting rule seed truth tapes hp
    menuSeed stage bit hactive hcursor hbit]
  exact ite_eq_right (by simpa only [beq_iff_eq] using hwrong)


theorem menu_run_correct_advance (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools))
    (sample : P.CalibratedMenuSeed × (P.freshInput P.certificate.stages P.tools fee hfee).World)
    (stage : (freshInstance P.certificate.stages P.tools).Stage) (clock : ℕ)
    (hactive : (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).halted = false)
    (hcursor : (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).cursor = stage.val)
    (hbit : (run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.written stage =
      some ((run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.truth stage)) :
    let state := run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample clock
    run (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) sample (clock + 1) =
      record accounting state (.advance stage) [.advanced stage] (advanceLedger state stage) (state.cursor + 1) false := by
  let input := P.freshInput P.certificate.stages P.tools fee hfee
  let rule := menuRule P table
  have hp := run_prefix_of_active input C .uncapped accounting rule
    (menuRule_legal P table fee hfee C hearly accounting) sample clock hactive
  have haction := menuRule_written_correct P table fee hfee C hearly accounting rule sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) hp sample.1 stage hactive hcursor hbit
  have haction' : rule sample.1 (run input C .uncapped accounting rule sample clock).history = .advance stage := haction
  apply run_succ_of_step input C .uncapped accounting rule sample clock _ hactive
  rw [haction']
  exact Step.advance _ stage ⟨hactive, hcursor⟩ (by rw [hbit]; exact Option.some_ne_none _) (.inl rfl)


end PDROC.CalibratedRuntime
