module

public import Paid.PDCompute_CoreEmit_Composition_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (HeapList linearExecute)

/-- True31-op original solve-record output: actual live rational price
and actual runtime-addressed original table, all on ONE fetched trace. -/
theorem solve_trace (program : Program) (input : List Cell) (origin returnPC : ℕ)
    (before : State) (n k M : ℕ) (upper : Bool) (solution : MultiplierSolve)
    (position : before.pc=origin) (dimensions : PreparedDimensions before n k M)
    (payload : SolvePayload before n k M upper solution)
    (fetch : FetchesCode program origin (solveCode origin upper returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤135*(encodeTable solution.table).length+420 ∧ after.pc=returnPC ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output++encodeSolve solution ∧
      (∀ state∈trace,RootD27.Core.EmittedPrefix before (encodeSolve solution) state) ∧
      peakCells trace≤workingCells before+(encodeSolve solution).length := by
  let price:=Cell.rational solution.multiplier
  let cells:=encodeTable solution.table
  let paid:=outputSlotResult before (priceSlot upper) price
  let ready:=pointerResult paid n k M cells.length upper
  have literal:=fetch
  rw [solveCode] at literal
  have priceFetch : FetchesCode program before.pc (outputSlotCode (priceSlot upper)) := by
    rw [position]
    exact literal.append_left.append_left
  obtain ⟨priceTrace,priceHead,priceLast,priceChain,priceTime,pricePrefixes⟩:=
    outputSlot_trace program input before (priceSlot upper) price payload.1 priceFetch
  have pointerFetch : FetchesCode program paid.pc (pointerCode upper) := by
    simpa only [paid,outputSlotResult,position,outputSlot_length] using literal.append_left.append_right
  obtain ⟨pointerTrace,pointerHead,pointerLast,pointerChain,pointerTime,pointerMemory⟩:=
    pointer_trace program input paid n k M cells.length upper dimensions payload.2.1 pointerFetch
  have emitFetch : FetchesCode program (origin+24) (RootD27.Core.emitHeapCode (origin+24) returnPC) := by
    simpa only [List.length_append,outputSlot_length,pointer_length] using literal.append_right
  have readyPC : ready.pc=origin+24 := by
    change before.pc+3+21=origin+24
    rw [position]
  obtain ⟨emitted,after,emitHead,emitLast,emitChain,emitTime,afterPC,_,_,afterHeap,afterLive,afterOutput,emitPrefix⟩:=
    RootD27.Core.emitHeap_actual program input (origin+24) returnPC emitFetch cells ready (bufferBase n k M upper)
      readyPC rfl rfl payload.2.2
  have first:=joinTrace_spec program input priceTrace pointerTrace before paid ready 60 330
    priceHead priceLast pointerHead pointerLast priceChain pointerChain priceTime pointerTime
  have joined:=joinTrace_spec program input (joinTrace priceTrace pointerTrace) emitted before ready after
    (60+330) (135*cells.length+30) first.1 first.2.1 emitHead emitLast first.2.2.1 emitChain first.2.2.2 emitTime
  have allPrefixes : ∀ state∈joinTrace (joinTrace priceTrace pointerTrace) emitted,
      RootD27.Core.EmittedPrefix before (encodeSolve solution) state := by
    intro state member
    rcases RootD27.Core.joinTrace_member member with earlier|outputting
    · rcases RootD27.Core.joinTrace_member earlier with pricing|pointing
      · exact emitted_extend before state [price] cells (pricePrefixes state pricing).1
      · have memory:=pointerMemory state pointing
        exact ⟨memory.1,memory.2.1,[price],cells,rfl,memory.2.2.1⟩
    · exact emitted_prepend before ready state [price] cells rfl rfl rfl (emitPrefix state outputting)
  refine ⟨joinTrace (joinTrace priceTrace pointerTrace) emitted,after,joined.1,joined.2.1,joined.2.2.1,
    ?_,afterPC,afterHeap,afterLive,?_,allPrefixes,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _
      (fun state member=>PDCompute.Solver.solver_emitted_workingCells (allPrefixes state member))⟩
  · exact joined.2.2.2.trans_eq (by ring)
  · change after.output=(before.output++[price])++cells at afterOutput
    change after.output=before.output++([price]++cells)
    simpa only [List.append_assoc] using afterOutput

end PDCompute.CoreEmit
