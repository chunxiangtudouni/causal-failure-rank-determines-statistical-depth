module
public import Paid.PDCompute_CorePrelude_Budget_003
public import Paid.PDROC_CalibrationRow_OperandPrefix_002
public import Paid.PDLower_CalibrationCompute_IOBits_088

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section

namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits PDCompute.CoreSearchBudget
open PDCompute.Solver PDMenu.ComputeFrame RootD27.Core RootD27.Bits
open PDROC.CalibrationRow.Operand
open PDLower.CalibrationCompute (linearExecute)

/-- The three original instructions really read ROM and allocate one live
heap cell. The loaded value is charged to the same incoming budget. -/
theorem input_slot_resources (program : Program) (input : List Cell) (before : State)
    (slot budget : ℕ) (value : Cell) (payload : input[slot]?=some value)
    (safe : SafeBits before budget) (valueBits : value.bits≤budget)
    (addressBits : (Cell.natural slot).bits≤budget)
    (pcBits : natBits (before.pc+3)≤budget)
    (fetch : FetchesCode program before.pc (inputSlotCode slot)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (inputSlotResult before slot value) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤60 ∧
      (∀ state∈trace,RegionMemory before state {slot} ∧ SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+3) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+3) := by
  let pointed:=({before with pc:=before.pc+1}).set .address (.natural slot)
  let loaded:=({pointed with pc:=pointed.pc+1}).set .value value
  have pointedSafe : SafeBits pointed budget:=
    (safe.withPC _ ((natBits_mono (by omega : before.pc+1≤before.pc+3)).trans pcBits)).set
      .address (.natural slot) addressBits
  have loadedSafe : SafeBits loaded budget:=
    (pointedSafe.withPC _ ((natBits_mono (by change before.pc+1+1≤before.pc+3;omega)).trans pcBits)).set
      .value value valueBits
  have loadRun : Instruction.execute input (.loadInput .value .address) pointed=some loaded:=by
    simp [Instruction.execute,pointed,loaded,State.set,Cell.nat?,payload]
  have storeSafe:=PrefixSafe.store input loaded budget .address .value slot loadedSafe
    (by simp [loaded,pointed,State.set])
    (by simpa only [loaded,pointed,State.set,Nat.add_assoc] using pcBits)
  have bits : PrefixSafe input (inputSlotCode slot) before budget:=
    PrefixSafe.cons input (.constant .address (.natural slot)) _ before pointed budget rfl safe
      (PrefixSafe.cons input (.loadInput .value .address) _ pointed loaded budget loadRun pointedSafe storeSafe)
  have run:=inputSlot_execute input before slot value payload
  obtain ⟨trace,head,last,chain,cost,prefixes,scope⟩:=linearExecute_trace_closedPC program input
    (inputSlotCode slot) (inputSlot_straight slot) before _ fetch run
  refine ⟨trace,head,last,chain,by simpa only [inputSlot_length] using cost,?_,scope,?_⟩
  · intro state member
    have split:=List.dropLast_append_getLast? (inputSlotResult before slot value) (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,actual⟩:=prefixes state proper
      have memory:=inputSlot_prefix input before state slot count bound actual
      exact ⟨RegionMemory.of_unchanged _ memory.1 memory.2.1 memory.2.2,bits count state actual⟩
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact ⟨RootD27.Endpoint.endpoint_store_region before slot value {slot} (by simp),bits.final run⟩
  · intro state member
    obtain ⟨count,bound,actual⟩:=prefixes state member
    have straight : StraightCode ((inputSlotCode slot).take count):=
      fun instruction inside=>inputSlot_straight slot instruction (List.mem_of_mem_take inside)
    have position:=linearExecute_pc input _ straight before state actual
    simp only [List.length_take,Nat.min_eq_left bound.le] at position
    change count<3 at bound
    omega

/-- Original count-times-three loader; prefixes carry both the physical
write region and the SAME operand budget. Nothing preallocates Header48. -/
theorem input_copy_resources (program : Program) (input : List Cell) (before : State)
    (budget : ℕ) (safe : SafeBits before budget)
    (values : ∀ cell∈input,cell.bits≤budget) :
    ∀ count : ℕ, count ≤ input.length → (Cell.natural count).bits≤budget →
      natBits (before.pc+3*count)≤budget →
      FetchesCode program before.pc (inputCopyCode count) →
      ∃ trace : List State,
        trace.head?=some before ∧ trace.getLast?=some (inputCopyResult input before count) ∧
        trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤60*count+15 ∧
        (∀ state∈trace,RegionMemory before state (Finset.range count) ∧ SafeBits state budget) ∧
        (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+3*count) ∧
        (∀ state∈trace.dropLast,state.pc<before.pc+3*count) := by
  intro count
  induction count with
  | zero =>
    intro _ _ _ _
    refine ⟨[before],rfl,rfl,.singleton before,?_,?_,?_,?_⟩
    · simpa only [Nat.mul_zero,Nat.zero_add] using time_singleton_le program before
    · intro state member
      have same:=List.mem_singleton.mp member
      subst state
      exact ⟨RegionMemory.refl _ _,safe⟩
    · intro state member
      have same:=List.mem_singleton.mp member
      subst state
      simp
    · simp
  | succ count ih =>
    intro bound addressBits pcBits fetch
    have priorAddress : (Cell.natural count).bits≤budget:=by
      change 1+natBits count≤_
      exact (Nat.add_le_add_left (natBits_mono (by omega : count≤count+1)) 1).trans addressBits
    obtain ⟨first,fh,fl,fc,ft,firstResources,firstScope,_⟩:=ih (by omega) priorAddress
      ((natBits_mono (by omega : before.pc+3*count≤before.pc+3*(count+1))).trans pcBits) fetch.append_left
    let middle:=inputCopyResult input before count
    have inside : count< input.length:=by omega
    let value:=(input[count]?).getD (.natural 0)
    have payload : input[count]?=some value:=by simp only [value,List.getElem?_eq_getElem inside,Option.getD_some]
    have valueMember : value∈input:=List.mem_of_getElem? payload
    have laterFetch : FetchesCode program middle.pc (inputSlotCode count):=by
      simpa only [middle,inputCopy_pc,inputCopy_length] using fetch.append_right
    obtain ⟨later,lh,ll,lc,lt,laterResources,laterScope,laterProper⟩:=input_slot_resources program input middle
      count budget value payload (firstResources middle (List.mem_of_getLast? fl)).2
      (values value valueMember) priorAddress
      (by simpa only [middle,inputCopy_pc,Nat.mul_succ,Nat.add_assoc] using pcBits) laterFetch
    have joined:=joinTrace_spec program input first later before middle _ (60*count+15) 60 fh fl lh ll fc lc ft lt
    have oldRegion : Finset.range count⊆Finset.range (count+1):=by
      intro address member
      exact Finset.mem_range.mpr (by have old:=Finset.mem_range.mp member;omega)
    have newRegion : ({count} : Finset ℕ)⊆Finset.range (count+1):=by simp
    have memory:=RegionMemory.join_trace first later before middle _ fl
      (fun state member=>(firstResources state member).1.enlarge oldRegion)
      (fun state member=>(laterResources state member).1.enlarge newRegion)
    have allSafe:=PDCompute.Pack.joinTrace_invariant first later (fun state=>SafeBits state budget)
      (fun state member=>(firstResources state member).2) (fun state member=>(laterResources state member).2)
    refine ⟨joinTrace first later,joined.1,joined.2.1,joined.2.2.1,
      joined.2.2.2.trans_eq (inputCopy_budget_succ count),
      fun state member=>⟨memory state member,allSafe state member⟩,?_,?_⟩
    · intro state member
      rcases joinTrace_member member with earlier|following
      · have scope:=firstScope state earlier
        omega
      · have scope:=laterScope state following
        have middlePC:=inputCopy_pc input before count
        change middle.pc=before.pc+3*count at middlePC
        omega
    · apply solverJoinTrace_proper first later middle (fun state=>state.pc<before.pc+3*(count+1)) fl lh
      · intro state member
        have scope:=firstScope state member
        omega
      · intro state member
        have proper:=laterProper state member
        have middlePC:=inputCopy_pc input before count
        change middle.pc=before.pc+3*count at middlePC
        omega

/-- Genuine zero-heap/zero-register initial state and the thirteen original
readonly cells suffice for the literal39-op physical loading prefix. -/
theorem prepared_loader_resources (P : Parameters) (fee : ℚ) (program : Program)
    (fetch : FetchesCode program 0 (inputCopyCode 13)) :
    ∃ trace : List State,
      trace.head?=some initial ∧ trace.getLast?=some (inputCopyResult (preparedInput P fee) initial 13) ∧
      trace.IsChain (fun first later=>step program (preparedInput P fee) first=some later) ∧
      time program trace≤795 ∧
      (∀ state∈trace,RegionMemory initial state (Finset.range 13) ∧ SafeBits state (inputBudget P fee)) ∧
      (∀ state∈trace,state.pc≤39) ∧ (∀ state∈trace.dropLast,state.pc<39) ∧
      PDLower.CalibrationCompute.HeapList (inputCopyResult (preparedInput P fee) initial 13) 0 (preparedInput P fee) := by
  have positive:=coreOperandBound_positive P fee
  have small : 64≤ inputBudget P fee:=by unfold inputBudget;omega
  have initialSafe : SafeBits initial 2:=by
    apply SafeBits.of_fields
    · intro register;change (Cell.natural 0).bits≤2;decide
    · intro address member;change address∈(∅ : Finset ℕ) at member;simp at member
    · intro address member;change address∈(∅ : Finset ℕ) at member;simp at member
    · intro value member;change value∈([] : List Cell) at member;cases member
    · change natBits 0≤2;decide
  obtain ⟨trace,head,last,chain,cost,resources,scope,proper⟩:=input_copy_resources program (preparedInput P fee) initial
    (inputBudget P fee) (PDCompute.Pack.safeBits_mono initialSafe (by omega))
    (fun cell member=>(prepared_input_cell_bits P fee cell member).trans (by unfold inputBudget;omega))
    13 (by simp [preparedInput,rawInput])
    ((by decide : (Cell.natural 13).bits≤64).trans small)
    ((by decide : natBits (initial.pc+3*13)≤64).trans small) fetch
  refine ⟨trace,head,last,chain,cost,resources,fun state member=>(scope state member).2,proper,?_⟩
  have stored:=inputCopy_heapList (preparedInput P fee) initial 13
  simpa only [PDCompute.Solver.HeapList,PDLower.CalibrationCompute.HeapList,
    List.take_of_length_le (by simp [preparedInput,rawInput] : (preparedInput P fee).length≤13)] using stored

end PDCompute.CorePrelude
