module
public import Paid.PDCompute_CoreFinalization_Trace_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
@[expose] public section
namespace PDCompute.CoreFinalization
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop
open PDCompute.CoreSearchBudget

theorem time_arithmetic (length entries : ℕ) (bounded : length≤16*entries+3) (positive : 1≤entries) :
    4000+1024*(length+2)≤32768*entries := by omega

/-- Original P/fee alone pay every internal finalization guard at the
already fixed global B. Only the real current phase's SafeBits is carried;
no payload, selector value or branch/resource oracle is an input. -/
theorem original_result (P : Parameters) (fee : ℚ) (program : Program) (labels : RoutineLabels)
    (input : List Cell) (origin pcUpper : ℕ) (before : State) (position : before.pc=origin)
    (ready : Ready P fee before) (represented : SearchStateRep P fee before (P.buildCachedFrontend fee).state)
    (safe : RootD27.Bits.SafeBits before (PDCompute.CoreGlobalBudget.budget P fee pcUpper))
    (endBound : origin+252≤pcUpper) (belowEntry : origin+252≤labels.solveEntry)
    (fetched : FetchesCode program origin (finalizationCode origin)) :
    Nonempty (Result program labels input P fee (P.buildCachedFrontend fee)
      (PDCompute.CoreGlobalBudget.budget P fee pcUpper) origin before) := by
  have rooms:=PDCompute.CoreGlobalBudget.original_final_rooms P fee pcUpper
  have bracketFields : ∀ lower upper,(P.buildCachedFrontend fee).state=.bracket lower upper→
      ScalarInputBits P fee lower upper (originalScalarScale P fee) := by
    intro lower upper equality
    have fields:=rooms.1
    rw [equality] at fields
    exact fields
  have capBits : 1+natBits (PDLower.CoreRuntimeNumeric.runtimeAddressLimit P)≤
      PDCompute.CoreGlobalBudget.budget P fee pcUpper :=
    PDCompute.CoreGlobalBudget.budget_runtime_natural P fee pcUpper _ (le_refl _)
  have addressBits : 1+natBits headerWords≤PDCompute.CoreGlobalBudget.budget P fee pcUpper :=
    PDCompute.CoreGlobalBudget.budget_header P fee pcUpper headerWords (by decide)
  exact given_budget P fee (P.buildCachedFrontend fee) program labels input origin before
    (originalScalarScale P fee) (PDCompute.CoreGlobalBudget.budget P fee pcUpper) position ready represented safe
    (PDCompute.CoreGlobalBudget.budget_small P fee pcUpper) bracketFields rooms.2.2.2 addressBits capBits
    (PDCompute.CoreGlobalBudget.budget_pc P fee pcUpper (origin+252) endBound) belowEntry fetched

/-- Complete original252 ending at its REAL HALT251, immediately before
the solver stub when origin+252=solveEntry. Every guard is discharged by
the original input's ONE global budget, not added as a new qualification. -/
theorem original_actual (P : Parameters) (fee : ℚ) (program : Program) (labels : RoutineLabels)
    (input : List Cell) (origin pcUpper : ℕ) (before : State) (position : before.pc=origin)
    (ready : Ready P fee before) (represented : SearchStateRep P fee before (P.buildCachedFrontend fee).state)
    (safe : RootD27.Bits.SafeBits before (PDCompute.CoreGlobalBudget.budget P fee pcUpper))
    (endBound : origin+252≤pcUpper) (belowEntry : origin+252≤labels.solveEntry)
    (fetched : FetchesCode program origin (finalizationCode origin)) :
    ∃ trace : List State,∃ selected after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤32768*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      selected∈trace ∧ selected.pc=origin+180 ∧
      selected.heap 29=.rational (selectorWeightRat P fee (P.buildCachedFrontend fee)) ∧
      after.heap=selected.heap ∧ after.live=selected.live ∧ after.live=before.live ∧
      after.heap 28=before.heap 28 ∧
      after.output=before.output++(encodeState (P.buildCachedFrontend fee).state++
        [.rational (selectorWeightRat P fee (P.buildCachedFrontend fee))]) ∧
      after.pc=origin+251 ∧ program[after.pc]?=some .halt ∧ step program input after=none ∧
      (∀ state∈trace,OutputRegion before (emittedCells P fee (P.buildCachedFrontend fee)) state) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state (PDCompute.CoreGlobalBudget.budget P fee pcUpper)) ∧
      peakCells trace≤workingCells before+16*PDCompute.Solver.entryCount P.certificate.stages P.tools+4 ∧
      peakOperandBits trace≤PDCompute.CoreGlobalBudget.budget P fee pcUpper ∧
      (∀ state∈trace,state.output.length≤before.output.length+16*PDCompute.Solver.entryCount P.certificate.stages P.tools+4) ∧
      (∀ state∈trace,origin≤state.pc ∧ state.pc≤origin+251) ∧
      (∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+251) ∧
      (∀ state∈trace,origin≤state.pc ∧ state.pc<labels.solveEntry) ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 ∧
      SolverCallRefinement program labels P fee 40000 trace := by
  obtain ⟨result⟩:=original_result P fee program labels input origin pcUpper before position ready represented safe
    endBound belowEntry fetched
  have length:=represented_state_length P fee (P.buildCachedFrontend fee).state before represented
  have cellsLength : (emittedCells P fee (P.buildCachedFrontend fee)).length≤
      16*PDCompute.Solver.entryCount P.certificate.stages P.tools+4 := by
    simp only [emittedCells,List.length_append,List.length_cons,List.length_nil]
    omega
  have positive : 0<PDCompute.Solver.entryCount P.certificate.stages P.tools := by
    unfold PDCompute.Solver.entryCount
    positivity
  have finalFrame:=result.frames result.after (List.mem_of_getLast? result.last)
  have cost:=result.timeBound.trans (time_arithmetic _ _ length (Nat.succ_le_of_lt positive))
  have peak:=result.space.trans (Nat.add_le_add_left cellsLength (workingCells before))
  have outputBound : ∀ state∈result.trace,state.output.length≤before.output.length+
      16*PDCompute.Solver.entryCount P.certificate.stages P.tools+4 := by
    intro state member
    simpa only [Nat.add_assoc] using
      ((result.frames state member).output_length).trans (Nat.add_le_add_left cellsLength before.output.length)
  refine ⟨result.trace,result.selected,result.after,result.head,result.last,result.chain,
    cost,result.selectedMember,result.selectedPC,result.selectedWeight,result.heap,result.live,
    finalFrame.live,result.counter,result.output,result.pc,result.halt,result.stopped,result.frames,result.safe,
    by simpa only [Nat.add_assoc] using peak,result.bits,outputBound,result.scope,result.proper,result.below,
    result.requests,result.count,result.refinement⟩

end PDCompute.CoreFinalization
