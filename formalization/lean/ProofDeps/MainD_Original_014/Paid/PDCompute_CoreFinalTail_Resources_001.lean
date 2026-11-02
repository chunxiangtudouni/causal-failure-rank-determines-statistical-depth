module
public import Paid.PDCompute_CoreEmit_Resources_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section

namespace PDCompute.CoreFinalTail
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDROC.DataBits
open PDCompute.CoreEmit
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute)

/-- Actual68-op state emission, actual heap29 output3, actual HALT1. -/
def code (origin : ℕ) : List Instruction :=
  stateCode origin (origin+68)++(outputSlotCode 29++[.halt])

theorem code_length (origin : ℕ) : (code origin).length=72 := by
  simp only [code,List.length_append,state_length,outputSlot_length,List.length_cons,List.length_nil]

theorem halt_fetch (program : Program) (origin : ℕ) (fetched : FetchesCode program origin (code origin)) :
    program[origin+71]?=some .halt := by
  have actual:=fetched.append_right.append_right
  have found:=actual 0 (by decide)
  norm_num [state_length,outputSlot_length,Nat.add_assoc] at found
  exact found

/-- The exact three real selector instructions reuse frozen012's
successful-prefix SafeBits. Its output word comes from the live heap. -/
theorem selector_trace_resources (program : Program) (input : List Cell) (before : State)
    (weight : ℚ) (budget : ℕ) (stored : HeapList before 29 [.rational weight])
    (safe : RootD27.Bits.SafeBits before budget) (addressBits : 1+natBits 29≤budget)
    (pcBits : natBits (before.pc+3)≤budget)
    (fetch : FetchesCode program before.pc (outputSlotCode 29)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (outputSlotResult before 29 (.rational weight)) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤60 ∧
      (∀ current∈trace,RootD27.Core.EmittedPrefix before [.rational weight] current ∧ RootD27.Bits.SafeBits current budget) ∧
      (∀ current∈trace,before.pc≤current.pc ∧ current.pc≤before.pc+3) ∧
      (∀ current∈trace.dropLast,current.pc<before.pc+3) := by
  let after:=outputSlotResult before 29 (.rational weight)
  have executed:=outputSlot_execute input before 29 (.rational weight) stored
  have bounded:=outputSlot_prefix_safe input before 29 budget (.rational weight) stored safe addressBits pcBits
  obtain ⟨trace,head,last,chain,cost,prefixes,location⟩:=linearExecute_trace_closedPC program input (outputSlotCode 29)
    (outputSlot_straight 29) before after fetch executed
  refine ⟨trace,head,last,chain,by simpa only [outputSlot_length] using cost,?_,
    by simpa only [outputSlot_length] using location,?_⟩
  · intro current member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    have actualPrefix : ∃ count≤3,linearExecute input ((outputSlotCode 29).take count) before=some current := by
      rw [←split] at member
      rcases List.mem_append.mp member with proper|terminal
      · obtain ⟨count,inside,actual⟩:=prefixes current proper
        exact ⟨count,by simpa only [outputSlot_length] using inside.le,actual⟩
      · have same:=List.mem_singleton.mp terminal
        subst current
        exact ⟨3,le_refl _,executed⟩
    obtain ⟨count,inside,actual⟩:=actualPrefix
    exact ⟨outputSlot_prefix input before current 29 count (.rational weight) stored inside actual,bounded count current actual⟩
  · intro current member
    obtain ⟨count,inside,actual⟩:=prefixes current member
    have straight : StraightCode ((outputSlotCode 29).take count):=
      fun instruction member=>outputSlot_straight 29 instruction (List.mem_of_mem_take member)
    have position:=linearExecute_pc input _ straight before current actual
    simp only [List.length_take,Nat.min_eq_left inside.le] at position
    rw [outputSlot_length] at inside
    omega

/-- Real72-op final tail on ONE trace and SAME GIVEN B. The final state
fetches HALT and truly has no successor; no free EOF is assumed. -/
theorem tail_trace_resources (program : Program) (input : List Cell) (origin : ℕ)
    (before : State) (n k M cap budget : ℕ) (state : MultiplierState) (weight : ℚ)
    (position : before.pc=origin) (dimensions : PreparedDimensions before n k M)
    (payload : StatePayload before n k M state) (selector : HeapList before 29 [.rational weight])
    (safe : RootD27.Bits.SafeBits before budget) (ends : StateEndBound n k M cap state)
    (capBits : 1+natBits cap≤budget) (counter : natBits (origin+72)≤budget)
    (fetched : FetchesCode program origin (code origin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤1024*((encodeState state).length+2) ∧
      after.pc=origin+71 ∧ program[after.pc]?=some .halt ∧ step program input after=none ∧
      after.heap=before.heap ∧ after.live=before.live ∧
      after.output=before.output++(encodeState state++[.rational weight]) ∧
      (∀ current∈trace,RootD27.Core.EmittedPrefix before (encodeState state++[.rational weight]) current) ∧
      peakCells trace≤workingCells before+(encodeState state).length+1 ∧
      peakOperandBits trace≤budget ∧ (∀ current∈trace,RootD27.Bits.SafeBits current budget) ∧
      (∀ current∈trace.dropLast,origin≤current.pc ∧ current.pc<origin+71) := by
  have capLower : 29≤cap := by
    cases state with
    | exact solution =>
      unfold StateEndBound bufferBase RootD27.Core.retainedTableBase at ends
      simp only [Bool.false_eq_true,ite_false] at ends
      omega
    | bracket lower upper =>
      have bound:=ends.1
      unfold bufferBase RootD27.Core.retainedTableBase at bound
      simp only [Bool.false_eq_true,ite_false] at bound
      omega
  have selectorAddress : 1+natBits 29≤budget :=
    (Nat.add_le_add_left (natBits_mono capLower) 1).trans capBits
  have emitCounter : natBits (origin+68)≤budget := (natBits_mono (by omega : origin+68≤origin+72)).trans counter
  have literal:=fetched
  rw [code] at literal
  obtain ⟨emitting,middle,eh,el,ec,et,middlePC,middleHeap,middleLive,middleOutput,emitted,_emitPeak,emitScope,_emitBits,emitSafe⟩:=
    state_trace_resources program input origin (origin+68) before n k M cap budget state position dimensions payload safe ends capBits
      emitCounter emitCounter (Or.inr (le_refl _)) literal.append_left
  have selectorStored : HeapList middle 29 [.rational weight]:=heapList_same selector middleHeap middleLive
  have selectorFetch : FetchesCode program middle.pc (outputSlotCode 29) := by
    rw [middlePC]
    simpa only [state_length] using literal.append_right.append_left
  obtain ⟨selecting,sh,sl,sc,st,selected,selectorScope,selectorProper⟩:=
    selector_trace_resources program input middle weight budget selectorStored
      (emitSafe middle (List.mem_of_getLast? el)) selectorAddress
      ((natBits_mono (by rw [middlePC];omega : middle.pc+3≤origin+72)).trans counter) selectorFetch
  let after:=outputSlotResult middle 29 (.rational weight)
  have afterPC : after.pc=origin+71 := by change middle.pc+3=origin+71;omega
  have realHalt : program[after.pc]?=some .halt := by rw [afterPC];exact halt_fetch program origin fetched
  have halted : step program input after=none := by simp only [step,realHalt];rfl
  have joined:=joinTrace_spec program input emitting selecting before middle after
    (1024*((encodeState state).length+1)) 60 eh el sh sl ec sc et st
  have allPrefixes : ∀ current∈joinTrace emitting selecting,
      RootD27.Core.EmittedPrefix before (encodeState state++[.rational weight]) current := by
    intro current member
    rcases RootD27.Core.joinTrace_member member with prior|later
    · exact emitted_extend before current (encodeState state) [.rational weight] (emitted current prior)
    · exact emitted_prepend before middle current (encodeState state) [.rational weight]
        middleHeap middleLive middleOutput (selected current later).1
  have allSafe:=PDCompute.Pack.joinTrace_invariant emitting selecting (fun current=>RootD27.Bits.SafeBits current budget)
    emitSafe (fun current member=>(selected current member).2)
  have allSpace : ∀ current∈joinTrace emitting selecting,workingCells current≤workingCells before+(encodeState state).length+1 := by
    intro current member
    obtain ⟨_heap,live,written,pending,decomposition,output⟩:=allPrefixes current member
    have lengthBound : written.length≤(encodeState state).length+1 := by
      have length:=congrArg List.length decomposition
      simp only [List.length_append,List.length_cons,List.length_nil] at length
      omega
    unfold workingCells
    rw [live,output,List.length_append]
    omega
  have proper : ∀ current∈(joinTrace emitting selecting).dropLast,origin≤current.pc ∧ current.pc<origin+71 := by
    have nonempty : selecting≠[] := by intro empty;rw [empty] at sh;cases sh
    intro current member
    change current∈(emitting.dropLast++selecting).dropLast at member
    rw [List.dropLast_append_of_ne_nil nonempty] at member
    rcases List.mem_append.mp member with prior|later
    · have scope:=emitScope current prior
      exact ⟨scope.1,by omega⟩
    · have scope:=selectorScope current (List.mem_of_mem_dropLast later)
      have strict:=selectorProper current later
      exact ⟨by omega,by omega⟩
  refine ⟨joinTrace emitting selecting,after,joined.1,joined.2.1,joined.2.2.1,?_,afterPC,realHalt,halted,
    middleHeap,middleLive,?_,allPrefixes,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,
    PDCompute.Pack.safeBits_peak _ budget allSafe,allSafe,proper⟩
  · have cost:=joined.2.2.2
    omega
  · change middle.output++[.rational weight]=before.output++(encodeState state++[.rational weight])
    rw [middleOutput,List.append_assoc]

end PDCompute.CoreFinalTail
