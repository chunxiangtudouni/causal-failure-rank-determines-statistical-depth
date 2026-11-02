module

public import Paid.PDROC_D27Prepare_Program_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.D27Prepare.Program

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlotResult storeSlotResult)
open PDMenu.ComputeFrame

/-- Original five-instruction input macro, with no hidden input fields. -/
def inputSlotResult (before : State) (address : ℕ) (value : Cell) : State :=
  let addressed := ({before with pc:=before.pc+1}).set .address (.natural address)
  let loaded := ({addressed with pc:=addressed.pc+1}).set .total value
  storeSlotResult loaded 0 address .total

theorem inputSlot_execute (input : List Cell) (before : State) (address : ℕ) (value : Cell)
    (base : before.register .fresh=.natural 0) (cell : input[address]?=some value) :
    linearExecute input (inputSlot address) before=some (inputSlotResult before address value) := by
  simp [inputSlot,PDLower.CalibrationCompute.storeSlot,linearExecute,Instruction.execute,
    State.set,NatOp.eval,Cell.nat?,base,cell,inputSlotResult,storeSlotResult,Nat.add_assoc]

theorem inputSlotResult_fields (before : State) (address : ℕ) (value : Cell) :
    (inputSlotResult before address value).heap=Function.update before.heap address value ∧
    (inputSlotResult before address value).live=insert address before.live ∧
    (inputSlotResult before address value).register .fresh=before.register .fresh ∧
    (inputSlotResult before address value).pc=before.pc+5 ∧
    (inputSlotResult before address value).output=before.output := by
  simp [inputSlotResult,storeSlotResult,State.set]

def inputSequenceCode (addresses : List ℕ) : List Instruction := addresses.flatMap inputSlot

def inputSequenceEval (input : List Cell) : List ℕ → SlotMemory → Option SlotMemory
  | [],memory => some memory
  | address::rest,memory => (input[address]?).bind fun value =>
      inputSequenceEval input rest (memory.write address value)

theorem inputSlot_straight (address : ℕ) : StraightCode (inputSlot address) := by
  intro instruction member
  simp only [inputSlot,PDLower.CalibrationCompute.storeSlot,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at member
  rcases member with (h|h)|(h|h|h) <;> subst instruction <;> trivial

theorem inputSequence_straight (addresses : List ℕ) : StraightCode (inputSequenceCode addresses) := by
  intro instruction member
  obtain ⟨address,_,hinstruction⟩ := List.mem_flatMap.mp member
  exact inputSlot_straight address instruction hinstruction

theorem inputSequence_length (addresses : List ℕ) : (inputSequenceCode addresses).length=5*addresses.length := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp only [inputSequenceCode,List.flatMap_cons,List.length_append,List.length_cons] at ih ⊢
      change 5+(rest.flatMap inputSlot).length=5*(rest.length+1)
      omega

theorem inputSequence_realize (addresses : List ℕ) (input : List Cell) (before : State)
    (memory next : SlotMemory) (matched : MemoryMatch before memory)
    (heval : inputSequenceEval input addresses memory=some next) :
    ∃ after : State, linearExecute input (inputSequenceCode addresses) before=some after ∧
      MemoryMatch after next ∧ after.output=before.output ∧
      after.pc=before.pc+(inputSequenceCode addresses).length := by
  induction addresses generalizing before memory with
  | nil =>
      have hn : memory=next := Option.some.inj heval
      subst next
      exact ⟨before,rfl,matched,rfl,by simp [inputSequenceCode]⟩
  | cons address rest ih =>
      obtain ⟨value,hcell,hrest⟩ := Option.bind_eq_some_iff.mp heval
      let middle := inputSlotResult before address value
      have fields := inputSlotResult_fields before address value
      have matchedMiddle : MemoryMatch middle (memory.write address value) :=
        MemoryMatch.write_of_fields before middle memory address value matched fields.1 fields.2.1 fields.2.2.1
      obtain ⟨after,hcode,hmatch,houtput,hpc⟩ := ih middle (memory.write address value) matchedMiddle hrest
      refine ⟨after,?_,hmatch,houtput.trans fields.2.2.2.2,?_⟩
      · simpa only [inputSequenceCode,List.flatMap_cons,PDLower.CalibrationCompute.linearExecute_append,
          inputSlot_execute input before address value matched.base hcell,Option.bind_some] using hcode
      · rw [inputSequence_length] at hpc ⊢
        have middlepc : middle.pc=before.pc+5 := fields.2.2.2.1
        simp only [List.length_cons]
        omega

/-- One original output instruction follows the same actual three-instruction load. -/
def outputSlotResult (before : State) (address : ℕ) (value : Cell) : State :=
  let loaded := loadSlotResult before 0 address .total
  {loaded with pc:=loaded.pc+1,output:=loaded.output++[value]}

theorem outputSlot_execute (input : List Cell) (before : State) (address : ℕ) (value : Cell)
    (base : before.register .fresh=.natural 0) (live : address ∈ before.live)
    (cell : before.heap address=value) :
    linearExecute input (outputSlot address) before=some (outputSlotResult before address value) := by
  simp [outputSlot,PDLower.CalibrationCompute.loadSlot,linearExecute,Instruction.execute,
    State.set,NatOp.eval,Cell.nat?,base,live,cell,outputSlotResult,loadSlotResult,Nat.add_assoc]

theorem outputSlotResult_fields (before : State) (address : ℕ) (value : Cell) :
    (outputSlotResult before address value).heap=before.heap ∧
    (outputSlotResult before address value).live=before.live ∧
    (outputSlotResult before address value).register .fresh=before.register .fresh ∧
    (outputSlotResult before address value).pc=before.pc+4 ∧
    (outputSlotResult before address value).output=before.output++[value] := by
  simp [outputSlotResult,loadSlotResult]

theorem outputSlot_straight (address : ℕ) : StraightCode (outputSlot address) := by
  intro instruction member
  simp only [outputSlot,PDLower.CalibrationCompute.loadSlot,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at member
  rcases member with (h|h|h)|h <;> subst instruction <;> trivial

def outputSequenceCode (addresses : List ℕ) : List Instruction := addresses.flatMap outputSlot

theorem outputSequence_straight (addresses : List ℕ) : StraightCode (outputSequenceCode addresses) := by
  intro instruction member
  obtain ⟨address,_,hinstruction⟩ := List.mem_flatMap.mp member
  exact outputSlot_straight address instruction hinstruction

theorem outputSequence_length (addresses : List ℕ) : (outputSequenceCode addresses).length=4*addresses.length := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp only [outputSequenceCode,List.flatMap_cons,List.length_append,List.length_cons] at ih ⊢
      change 4+(rest.flatMap outputSlot).length=4*(rest.length+1)
      omega

theorem outputSequence_realize (addresses : List ℕ) (input : List Cell) (before : State)
    (memory : SlotMemory) (matched : MemoryMatch before memory)
    (live : ∀ address ∈ addresses, address ∈ memory.present) :
    ∃ after : State, linearExecute input (outputSequenceCode addresses) before=some after ∧
      MemoryMatch after memory ∧ after.output=before.output++addresses.map memory.value ∧
      after.pc=before.pc+(outputSequenceCode addresses).length := by
  induction addresses generalizing before with
  | nil => exact ⟨before,rfl,matched,by simp,by simp [outputSequenceCode]⟩
  | cons address rest ih =>
      let middle := outputSlotResult before address (memory.value address)
      have fields := outputSlotResult_fields before address (memory.value address)
      have matchedMiddle : MemoryMatch middle memory :=
        ⟨fields.1.trans matched.heap,fields.2.1.trans matched.live,fields.2.2.1.trans matched.base⟩
      obtain ⟨after,hcode,hmatch,houtput,hpc⟩ := ih middle matchedMiddle (fun a ha => live a (by simp [ha]))
      refine ⟨after,?_,hmatch,?_,?_⟩
      · have hfirst := outputSlot_execute input before address (memory.value address) matched.base
          (by rw [matched.live]; exact live address (by simp)) (by rw [matched.heap])
        simpa only [outputSequenceCode,List.flatMap_cons,PDLower.CalibrationCompute.linearExecute_append,
          hfirst,Option.bind_some] using hcode
      · rw [houtput,fields.2.2.2.2]
        simp only [List.map_cons,List.append_assoc,List.singleton_append]
      · rw [outputSequence_length] at hpc ⊢
        have middlepc : middle.pc=before.pc+4 := fields.2.2.2.1
        simp only [List.length_cons]
        omega

/-- The final eval conjunct is derived from the actual chain and fetched halt. -/
theorem runs_of_actual_trace (input : List Cell) (trace : List State) (final : State)
    (head : trace.head?=some initial)
    (chain : trace.IsChain (fun first later => step program input first=some later))
    (last : trace.getLast?=some final) (halt : program[final.pc]?=some .halt) :
    Runs program input trace final := by
  refine ⟨head,chain,last,halt,StateTransition.mem_eval.mpr ⟨?_,?_⟩⟩
  · have nonempty : trace ≠ [] := by intro h; simp [h] at head
    have reached := List.relationReflTransGen_of_exists_isChain trace chain nonempty
    have head' : trace.head nonempty=initial := by
      have hh := List.head?_eq_some_head nonempty
      rw [head] at hh
      exact (Option.some.inj hh).symm
    have last' : trace.getLast nonempty=final := by
      have hl := List.getLast?_eq_getLast_of_ne_nil nonempty
      rw [last] at hl
      exact (Option.some.inj hl).symm
    simpa only [StateTransition.Reaches,head',last',Option.mem_def] using reached
  · simp [step,halt,Instruction.execute]

end PDROC.D27Prepare.Program
