module

public import PaperProofs.Retained.PRet_ExactTerminal_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetSourceTerminal002

open Common Common.Native PRetExactTerminal001
open scoped ENNReal BigOperators

variable {I : Instance}

/-- The specified pairs are the actual source execution records, including
their original order. No fresh matching or fee-minimizing tool is selected. -/
theorem source_pairs_trace (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    (hallocation : C.allocation = .terminalBarrier)
    (hexecution : C.execution = .terminalBarrier)
    (source : Ledger I) (hsource : LedgerWellFormed source)
    (s : State I) (hinvariant : Invariant C s) (hactive : s.halted = false)
    (htruth : s.ledger.truth = source.truth) (hwritten : s.ledger.written = source.written)
    (hcommit : s.ledger.commitments = []) (hexecute : s.ledger.executions = [])
    (hreported : ∀ e ∈ source.executions, ∃ clock, s.ledger.reportTime e.handle.stage = some clock) :
    ∃ t : State I, UncappedTrace input C accounting tapes s t ∧ Invariant C t ∧
      t.halted = false ∧ t.cursor = s.cursor ∧
      t.ledger.truth = s.ledger.truth ∧ t.ledger.written = s.ledger.written ∧
      t.ledger.executions.map executionPair = source.executions.map executionPair ∧
      t.ledger.actualBill input.fees = s.ledger.actualBill input.fees + source.correctionBill input.fees := by
  have hstages : ((source.executions.map executionPair).map Prod.fst).Nodup := by
    simpa only [List.map_map, Function.comp_def, executionPair] using hsource.execution_stages
  have htools : ((source.executions.map executionPair).map Prod.snd).Nodup := by
    simpa only [List.map_map, Function.comp_def, executionPair] using hsource.execution_tools
  have hcompatible : ∀ pair ∈ source.executions.map executionPair, pair.2 ∈ I.eligible pair.1 := by
    intro pair hpair
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpair
    exact hsource.compatible e he
  have hhandles : ∀ pair ∈ source.executions.map executionPair,
      validHandle s (originalHandle s pair.1) := by
    intro pair hpair
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpair
    refine ⟨?_, rfl, hreported e he⟩
    simpa only [executionPair, originalHandle, hwritten, htruth] using (hsource.genuine e he).1
  have hunused : ∀ pair ∈ source.executions.map executionPair,
      ∀ a ∈ s.ledger.commitments, a.tool ≠ pair.2 := by
    simp only [hcommit, List.not_mem_nil, forall_false, implies_true]
  have hunallocated : ∀ pair ∈ source.executions.map executionPair,
      ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ pair.1 := by
    simp only [hcommit, List.not_mem_nil, forall_false, implies_true]
  obtain ⟨t, htrace, hinvariantT, hactiveT, hcursorT, htruthT, hwrittenT, hpairsT, hfeeT⟩ :=
    replay_pairs input C accounting tapes hallocation hexecution s
      (source.executions.map executionPair) hstages htools hcompatible s hinvariant hactive
      hhandles hunused hunallocated
  refine ⟨t, htrace, hinvariantT, hactiveT, hcursorT, htruthT, hwrittenT, ?_, ?_⟩
  · simpa only [hexecute, List.map_nil, List.nil_append] using hpairsT
  · simpa only [List.map_map, Function.comp_def, executionPair, pairCharge, Ledger.correctionBill] using hfeeT

/-- A successful source's exact paid pairs give an actual successful terminal
completion of the clean destination. All preceding observation/variable
charges are retained; the final stop is a real Step. This state component
does not assume a supplied matching and does not prove policy rearrangement. -/
theorem successful_source_terminal (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    (hallocation : C.allocation = .terminalBarrier)
    (hexecution : C.execution = .terminalBarrier)
    (source : Ledger I) (hsource : LedgerWellFormed source) (hsuccess : source.success C)
    (s : State I) (hinvariant : Invariant C s) (hactive : s.halted = false)
    (hallwritten : allWritten s.ledger)
    (htruth : s.ledger.truth = source.truth) (hwritten : s.ledger.written = source.written)
    (hcommit : s.ledger.commitments = []) (hexecute : s.ledger.executions = [])
    (hreported : ∀ e ∈ source.executions, ∃ clock, s.ledger.reportTime e.handle.stage = some clock) :
    ∃ finished : State I, UncappedTrace input C accounting tapes s finished ∧
      Invariant C finished ∧ finished.halted = true ∧ finished.ledger.success C ∧
      finished.cursor = s.cursor ∧
      finished.ledger.executions.map executionPair = source.executions.map executionPair ∧
      finished.ledger.actualBill input.fees = s.ledger.actualBill input.fees + source.correctionBill input.fees := by
  obtain ⟨t, htrace, hinvariantT, hactiveT, hcursorT, htruthT, hwrittenT, hpairsT, hfeeT⟩ :=
    source_pairs_trace input C accounting tapes hallocation hexecution source hsource
      s hinvariant hactive htruth hwritten hcommit hexecute hreported
  let finished := stopState t false
  have hstop : Step input C .uncapped accounting tapes t .stop finished := .stop t hactiveT
  refine ⟨finished, htrace.trans (Relation.ReflTransGen.single ⟨.stop, hstop⟩),
    step_invariant input C .uncapped accounting tapes hstop hinvariantT, rfl, ?_, hcursorT, hpairsT, hfeeT⟩
  refine ⟨?_, rfl, ?_, ?_⟩
  · have ht : allWritten t.ledger := by simpa only [allWritten, hwrittenT] using hallwritten
    simp only [finished, stopState, ht, decide_true]
  · simp [Ledger.windowObligations, hallocation, hexecution]
  · intro stage
    rcases hsuccess.2.2.2 stage with hcorrect | ⟨e, he, hstage⟩
    · exact Or.inl (by simpa only [finished, stopState, hwrittenT, htruthT, hwritten, htruth] using hcorrect)
    · right
      have hpair : executionPair e ∈ t.ledger.executions.map executionPair := by
        rw [hpairsT]
        exact List.mem_map.mpr ⟨e, he, rfl⟩
      obtain ⟨e', he', heq⟩ := List.mem_map.mp hpair
      exact ⟨e', he', (congrArg Prod.fst heq).trans hstage⟩

end PaperProofs.Retained.PRetSourceTerminal002
