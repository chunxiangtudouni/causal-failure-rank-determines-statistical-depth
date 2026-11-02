module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_002
public import PaperProofs.Paid.PDMenu_MenuEntrySnapshot_076
public import PaperProofs.Paid.PDMenu_MenuPhysicalSnapshot_084
public import PaperProofs.Paid.PDMenu_MenuPastPhysical_100

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu

namespace PDROC.CalibratedRuntime

theorem menuRule_advance_good_or_executed (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*}
    (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {clock : ℕ} {state : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : P.CalibratedMenuSeed) (stage : P.sharedInstance.Stage)
    (ha : menuRule P table menuSeed state.history = .advance stage) :
    state.ledger.written stage = some (state.ledger.truth stage) ∨
      ∃ execution ∈ state.ledger.executions, execution.handle.stage = stage := by
  have hallowed : historyAllowsAction state.history (menuRule P table menuSeed state.history) := by
    let action : Action P.sharedInstance := P.calibratedMenuCandidate table menuSeed state.history
    change historyAllowsAction state.history
      (if historyAllowsAction state.history action then action else .abandon)
    split
    · assumption
    · trivial
  rw [ha] at hallowed
  change historyCursor state.history = stage.val ∧ historyWritten state.history stage ≠ none at hallowed
  obtain ⟨bit, serial, hw⟩ : ∃ bit serial, historyWrite state.history stage = some (bit, serial) := by
    cases hw : historyWrite state.history stage with
    | none => exact (hallowed.2 (by simp only [historyWritten, hw, Option.map_none])).elim
    | some pair => exact ⟨pair.1, pair.2, rfl⟩
  rw [menuRule_written_eq_original P table menuSeed state.history stage bit serial hallowed.1 hw] at ha
  exact PDMenu.menuPrefix_advance_good_or_executed P P.certificate.stages P.tools table fee hfee C hearly
    accounting rule seed truth tapes hp menuSeed.1 stage ha

theorem menuPrefix_pastSettled (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) (seed : P.CalibratedMenuSeed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) seed truth tapes clock state) : MenuPastSettled state := by
  classical
  induction hp with
  | initial =>
    intro a ha
    cases ha
  | @next clock state nextState hp hstep ih =>
    generalize haction : menuRule P table seed state.history = action at hstep
    cases hstep with
    | review => exact ih
    | write stage bit live port resources =>
      simpa only [MenuPastSettled, record, reportedWriteLedger, hC.1.1, ite_true, writeLedger] using ih
    | allocate handle tool active valid compatible unused unallocated window resources =>
      intro a ha hpast
      have hamem : a ∈ state.ledger.commitments ∨ a = ⟨handle, tool, state.clock⟩ := by
        change a ∈ state.ledger.commitments ++ [⟨handle, tool, state.clock⟩] at ha
        rcases List.mem_append.mp ha with hold | hnew
        · exact Or.inl hold
        · exact Or.inr (List.mem_singleton.mp hnew)
      rcases hamem with hold | rfl
      · exact ih a hold hpast
      · have hcursor := window hC.1.2
        change handle.stage.val < state.cursor at hpast
        omega
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      intro a ha hpast
      obtain ⟨e, he, hh, ht⟩ := ih a ha hpast
      exact ⟨e, List.mem_append_left _ he, hh, ht⟩
    | advance stage live written resources =>
      intro a ha hpast
      change a ∈ state.ledger.commitments at ha
      change a.handle.stage.val < state.cursor + 1 at hpast
      by_cases hbefore : a.handle.stage.val < state.cursor
      · exact ih a ha hbefore
      · have hs : a.handle.stage = stage := Fin.ext (by have hc := live.2; omega)
        have hwf := prefix_ledgerWellFormed (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
          (menuRule P table) seed truth tapes hp
        rcases menuRule_advance_good_or_executed P table fee hfee C hC.1.1 accounting
          (menuRule P table) seed truth tapes hp seed stage haction with hgood | hex
        · have hg := (prefix_invariant (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
            (menuRule P table) seed truth tapes hp).commitment_genuine a ha
          rw [hs, hgood] at hg
          have hfalse : state.ledger.truth stage = !state.ledger.truth stage := Option.some.inj hg.1
          exact False.elim ((Bool.eq_not_self _).mp hfalse)
        · obtain ⟨e, he, heStage⟩ := hex
          obtain ⟨b, hb, hhandle, htool, _⟩ := hwf.backed e he
          have hstage : b.handle.stage = a.handle.stage := (congrArg MismatchHandle.stage hhandle).trans (heStage.trans hs.symm)
          have hba : b = a := List.inj_on_of_nodup_map hwf.commitment_stages hb ha hstage
          subst b
          exact ⟨e, he, hhandle.symm, htool.symm⟩
    | stop | abandon => exact ih


theorem menuPrefix_allCommitmentsExecuted_beforeWrite (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) (seed : P.CalibratedMenuSeed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) seed truth tapes clock state)
    (stage : (freshInstance P.certificate.stages P.tools).Stage) (hcursor : state.cursor = stage.val)
    (hopen : state.ledger.written stage = none) :
    ∀ a ∈ state.ledger.commitments, ∃ e ∈ state.ledger.executions, e.handle = a.handle ∧ e.tool = a.tool := by
  have hinv := prefix_invariant (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) seed truth tapes hp
  have hcausal := prefix_cursorInvariant (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) seed truth tapes hp
  have hsettled := menuPrefix_pastSettled P table fee hfee C hC accounting seed truth tapes hp
  intro a ha
  apply hsettled a ha
  have hg := (hinv.commitment_genuine a ha).1
  by_contra hnot
  by_cases hfuture : state.cursor < a.handle.stage.val
  · rw [hcausal.future_written a.handle.stage hfuture] at hg
    cases hg
  · have hs : a.handle.stage = stage := Fin.ext (by omega)
    rw [hs, hopen] at hg
    cases hg


theorem menuPrefix_executions_beforeWrite (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools))
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) (seed : P.CalibratedMenuSeed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) seed truth tapes clock state)
    (stage : (freshInstance P.certificate.stages P.tools).Stage) (hcursor : state.cursor = stage.val)
    (hopen : state.ledger.written stage = none) :
    ∀ e ∈ state.ledger.executions, e.handle.stage.val < state.cursor := by
  have hinv := prefix_invariant (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) seed truth tapes hp
  have hcausal := prefix_cursorInvariant (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) seed truth tapes hp
  intro e he
  have hg := (hinv.wellFormed.genuine e he).1
  by_contra hnot
  by_cases hfuture : state.cursor < e.handle.stage.val
  · rw [hcausal.future_written e.handle.stage hfuture] at hg
    cases hg
  · have hs : e.handle.stage = stage := Fin.ext (by omega)
    rw [hs, hopen] at hg
    cases hg

/-- The original table snapshot is exactly the cardinality of genuinely
unused tools before writing a stage. Pending obligations cannot secretly
consume a tool from this state. -/

theorem menuPrefix_entryTools_eq_availableCard (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) (seed : P.CalibratedMenuSeed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) seed truth tapes clock state)
    (stage : (freshInstance P.certificate.stages P.tools).Stage) (hcursor : state.cursor = stage.val)
    (hopen : state.ledger.written stage = none) :
    P.menuEntryTools P.certificate.stages P.tools state.history stage = (Finset.univ \ historyUsed state.history).card := by
  classical
  have hwf := prefix_ledgerWellFormed (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) seed truth tapes hp
  have hsettled := menuPrefix_allCommitmentsExecuted_beforeWrite P table fee hfee C hC accounting seed truth tapes hp stage hcursor hopen
  have hbefore := menuPrefix_executions_beforeWrite P table fee hfee C accounting seed truth tapes hp stage hcursor hopen
  have hused : historyUsed state.history = (state.ledger.executions.map (·.tool)).toFinset := by
    rw [prefix_historyUsed (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting (menuRule P table) seed truth tapes hp]
    apply Finset.Subset.antisymm
    · intro tool ht
      obtain ⟨a, ha, hat⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      obtain ⟨e, he, _, het⟩ := hsettled a ha
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, het.trans hat⟩)
    · intro tool ht
      obtain ⟨e, he, het⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      obtain ⟨a, ha, _, hat, _⟩ := hwf.backed e he
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, hat.trans het⟩)
  have hfiltered : ((state.ledger.executions.map (fun e => (e.handle, e.tool))).filter
      (fun pair => pair.1.stage.val < stage.val)) = state.ledger.executions.map (fun e => (e.handle, e.tool)) := by
    apply List.filter_eq_self.mpr
    intro pair hpairs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpairs
    exact decide_eq_true ((hbefore e he).trans_eq hcursor)
  rw [Parameters.menuEntryTools, prefix_historyExecutions (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) seed truth tapes hp, hfiltered, List.length_map, hused,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    List.toFinset_card_of_nodup hwf.execution_tools, List.length_map]
  have hcard : Fintype.card (freshInstance P.certificate.stages P.tools).Tool = P.tools := Fintype.card_fin P.tools
  exact congrArg (fun count : ℕ => count - state.ledger.executions.length) hcard.symm


theorem menuPrefix_entryTools_eq_physical_sub (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools))
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) (seed : P.CalibratedMenuSeed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) seed truth tapes clock state)
    (stage : (freshInstance P.certificate.stages P.tools).Stage) (hcursor : state.cursor = stage.val)
    (hopen : state.ledger.written stage = none) :
    P.menuEntryTools P.certificate.stages P.tools state.history stage = P.tools - state.ledger.executions.length := by
  have hbefore := menuPrefix_executions_beforeWrite P table fee hfee C accounting seed truth tapes hp stage hcursor hopen
  have hfiltered : ((state.ledger.executions.map (fun e => (e.handle, e.tool))).filter
      (fun pair => pair.1.stage.val < stage.val)) = state.ledger.executions.map (fun e => (e.handle, e.tool)) := by
    apply List.filter_eq_self.mpr
    intro pair hpairs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpairs
    exact decide_eq_true ((hbefore e he).trans_eq hcursor)
  rw [Parameters.menuEntryTools, prefix_historyExecutions (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) seed truth tapes hp, hfiltered, List.length_map]


theorem menuPrefix_pastCorrect (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) (seed : P.CalibratedMenuSeed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) seed truth tapes clock state) :
    ∀ stage : (freshInstance P.certificate.stages P.tools).Stage, stage.val < state.cursor →
      state.ledger.written stage = some (state.ledger.truth stage) ∨
        ∃ execution ∈ state.ledger.executions, execution.handle.stage = stage := by
  induction hp with
  | initial => intro stage hs; exact (Nat.not_lt_zero _ hs).elim
  | @next clock state nextState hp step ih =>
    generalize haction : menuRule P table seed state.history = action at step
    cases step with
    | review => exact ih
    | write current bit live port resources =>
      intro stage hs
      have hne : stage ≠ current := by
        intro heq
        subst stage
        change current.val < state.cursor at hs
        have hc := live.2
        omega
      have hlookup : Function.update state.ledger.written current (some bit) stage = state.ledger.written stage :=
        Function.update_of_ne hne (some bit) state.ledger.written
      simp only [record, reportedWriteLedger, hearly, ite_true, writeLedger]
      rcases ih stage hs with hw | he
      · exact Or.inl (hlookup.trans hw)
      · exact Or.inr he
    | allocate => exact ih
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      intro stage hs
      rcases ih stage hs with hgood | ⟨execution, he, heStage⟩
      · exact Or.inl hgood
      · exact Or.inr ⟨execution, List.mem_append_left _ he, heStage⟩
    | advance current live written resources =>
      intro stage hs
      by_cases hold : stage.val < state.cursor
      · exact ih stage hold
      · have heq : stage = current := by
          apply Fin.ext
          change stage.val < state.cursor + 1 at hs
          have hc := live.2
          omega
        subst stage
        exact menuRule_advance_good_or_executed P table fee hfee C hearly accounting
          (menuRule P table) seed truth tapes hp seed current haction
    | stop | abandon => exact ih


theorem menuPrefix_terminal_allWritten (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) (seed : P.CalibratedMenuSeed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) seed truth tapes clock state)
    (hcursor : state.cursor = P.certificate.stages) : allWritten state.ledger := by
  have hgood := menuPrefix_pastCorrect P table fee hfee C hearly accounting seed truth tapes hp
  have hwf := prefix_ledgerWellFormed (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) seed truth tapes hp
  intro stage
  have hs : stage.val < state.cursor := by
    rw [hcursor]
    simpa [freshInstance] using stage.isLt
  rcases hgood stage hs with hc | ⟨execution, he, hs⟩
  · rw [hc]
    exact Option.some_ne_none _
  · have hw := (hwf.genuine execution he).1
    rw [hs] at hw
    rw [hw]
    exact Option.some_ne_none _


theorem menuPrefix_terminal_success (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance P.certificate.stages P.tools)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance P.certificate.stages P.tools)) (seed : P.CalibratedMenuSeed)
    (truth : (freshInstance P.certificate.stages P.tools).Stage → Bool) (tapes : ReviewTapes (P.freshInput P.certificate.stages P.tools fee hfee))
    {clock : ℕ} {state : State (freshInstance P.certificate.stages P.tools)}
    (hp : Prefix (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
      (menuRule P table) seed truth tapes clock state)
    (hcursor : state.cursor = P.certificate.stages) (hhalt : state.halted = true) (habandoned : state.ledger.abandoned = false) :
    state.ledger.success C := by
  have hall := menuPrefix_terminal_allWritten P table fee hfee C hearly accounting seed truth tapes hp hcursor
  have hf := prefix_halted_allWritten_finished (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) seed truth tapes hp hhalt hall
  apply (prefix_success_iff_physical (P.freshInput P.certificate.stages P.tools fee hfee) C .uncapped accounting
    (menuRule P table) seed truth tapes hp).mpr
  refine ⟨hf, habandoned, ?_⟩
  intro stage
  apply (finalOutput_correct_iff state.ledger stage).mpr
  apply menuPrefix_pastCorrect P table fee hfee C hearly accounting seed truth tapes hp stage
  rw [hcursor]
  simpa [freshInstance] using stage.isLt


end PDROC.CalibratedRuntime
