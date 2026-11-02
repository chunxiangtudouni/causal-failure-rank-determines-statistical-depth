module

public import Paid.PDROC_D27Prepare_Resources_009
public import Paid.PDROC_D27Prepare_Resources_010
public import Paid.PDROC_D27Prepare_Resources_013
public import Paid.PDROC_D27Prepare_Program_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDROC.D27Prepare.Program PDMenu.ComputeFrame

namespace PDROC.D27Prepare.Resources

theorem inputSequence_prefix_bounds (addresses : List ℕ) (input : List Cell)
    (before : State) (memory next : SlotMemory) (H B : ℕ)
    (matched : MemoryMatch before memory) (bounded : StateBounds H B before)
    (inside : ∀ address ∈ addresses, address < H) (addressBits : 1+natBits H ≤ B)
    (inputBits : ∀ cell ∈ input, cell.bits ≤ B)
    (executed : inputSequenceEval input addresses memory=some next) :
    LinearPrefixBounds input (inputSequenceCode addresses) before H B := by
  induction addresses generalizing before memory with
  | nil => exact LinearPrefixBounds.nil input bounded
  | cons address rest ih =>
    obtain ⟨value,fetched,later⟩ := Option.bind_eq_some_iff.mp executed
    let middle := inputSlotResult before address value
    have fields := inputSlotResult_fields before address value
    have actual := inputSlot_execute input before address value matched.base fetched
    have first := inputSlot_prefix_bounds input before address H B value bounded matched.base
      (inside address (by simp)) addressBits fetched (inputBits value (List.mem_of_getElem? fetched))
    have matchedMiddle : MemoryMatch middle (memory.write address value) :=
      MemoryMatch.write_of_fields before middle memory address value matched fields.1 fields.2.1 fields.2.2.1
    have restBound := ih middle (memory.write address value) matchedMiddle (first.final actual)
      (fun other member => inside other (by simp only [List.mem_cons]; exact Or.inr member)) later
    simpa only [inputSequenceCode,List.flatMap_cons] using
      LinearPrefixBounds.append input (inputSlot address) (inputSequenceCode rest) before middle H B
        actual first restBound

theorem MemoryMatch.memoryBounds (state : State) (memory : SlotMemory) (H B : ℕ)
    (matched : MemoryMatch state memory) (bounded : StateBounds H B state) : MemoryBounds H B memory := by
  constructor
  · simpa only [←matched.live] using bounded.live
  · intro address member
    have live : address ∈ state.live := by simpa only [matched.live] using member
    simpa only [matched.heap] using bounded.heapValues address live

theorem initialization_constants (B : ℕ) (enough : 6 ≤ B) :
    ∀ command ∈ initializationCommands, ∃ target value,
      command=SlotCommand.constant target value ∧ target<64 ∧ value.bits≤B := by
  intro command member
  simp only [initializationCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals refine ⟨_,_,rfl,by decide,?_⟩
  all_goals norm_num [Cell.bits,ratEncodingBits,ratNumBits,ratDenBits,natBits]
  all_goals omega

/-- The actual input loads and literal initialization are bounded at every
physical instruction, without a prepared certificate in the entry heap. -/
theorem prologue_prefix_bounds (c0 c1 c2 c3 c4 c5 : Cell) (B : ℕ)
    (enough : 8 ≤ B) (inputBits : ∀ cell ∈ sixInput c0 c1 c2 c3 c4 c5,cell.bits≤B) :
    LinearPrefixBounds (sixInput c0 c1 c2 c3 c4 c5) prologueBody initial 64 B := by
  let input := sixInput c0 c1 c2 c3 c4 c5
  let baseState := ({initial with pc:=1}).set .fresh (.natural 0)
  have baseMatch : MemoryMatch baseState emptySlotMemory := ⟨rfl,rfl,rfl⟩
  have initialBound := initial_bounds 64 B (by omega)
  have zeroBits : (Cell.natural 0).bits≤B := by norm_num [Cell.bits,natBits]; omega
  have baseBound : StateBounds 64 B baseState := (initialBound.with_pc 1).set _ _ zeroBits
  have baseExecute : linearExecute input [.constant .fresh (.natural 0)] initial=some baseState := rfl
  have basePrefix := single_prefix_bounds input (.constant .fresh (.natural 0)) initial baseState
    64 B initialBound baseBound rfl
  have addressBits : 1+natBits 64≤B := by
    simpa only [show 1+natBits 64=8 by decide] using enough
  obtain ⟨loaded,loadedRun,loadedMatch,_,_⟩ := inputSequence_realize (List.range 6) input baseState
    emptySlotMemory (loadedInputMemory c0 c1 c2 c3 c4 c5) baseMatch (input_memory_eval ..)
  have loadedPrefix := inputSequence_prefix_bounds (List.range 6) input baseState emptySlotMemory
    (loadedInputMemory c0 c1 c2 c3 c4 c5) 64 B baseMatch baseBound
    (fun address member => by have := List.mem_range.mp member; omega)
    addressBits inputBits (input_memory_eval ..)
  have loadedBound := loadedPrefix.final loadedRun
  have constants := initialization_constants B (by omega)
  have constantPrefix := slotSequence_prefix_bounds initializationCommands input loaded
    (loadedInputMemory c0 c1 c2 c3 c4 c5) (initializedInputMemory c0 c1 c2 c3 c4 c5)
    64 B loadedMatch loadedBound (constant_sequence_addresses _ 64 B constants)
    addressBits (initialization_eval _)
    (constant_sequence_memory_bounds _ _ 64 B
      (MemoryMatch.memoryBounds loaded _ 64 B loadedMatch loadedBound) constants)
  have later := LinearPrefixBounds.append input _ _ baseState loaded 64 B
    loadedRun loadedPrefix constantPrefix
  simpa only [prologueBody,List.append_assoc] using
    LinearPrefixBounds.append input [.constant .fresh (.natural 0)]
      (inputSequenceCode (List.range 6)++slotSequenceCode initializationCommands)
      initial baseState 64 B baseExecute basePrefix later

theorem raw_prologue_prefix_bounds (P : Parameters) (fee : ℚ) :
    LinearPrefixBounds (rawInput P fee) prologueBody initial 64 (operandBudget P fee) := by
  apply prologue_prefix_bounds
  · have h := operandBudget_address_bits P fee
    have address : 1+natBits 64=8 := by decide
    omega
  · exact rawInput_cell_bits P fee

end PDROC.D27Prepare.Resources
