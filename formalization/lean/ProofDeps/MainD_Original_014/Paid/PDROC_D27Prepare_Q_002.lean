module

public import Paid.PDROC_D27Prepare_Q_001
public import Paid.PDROC_D27Prepare_Memory_001
public import Paid.PDMenu_ComputeFrame_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program

namespace PDROC.D27Prepare.Q

def MemoryProgress (R : Finset ℕ) (before after : State) : Prop :=
  MemoryFrame R before after ∧ before.live ⊆ after.live

theorem MemoryProgress.refl (R : Finset ℕ) (state : State) : MemoryProgress R state state :=
  ⟨MemoryFrame.refl R state, fun _ member => member⟩

theorem MemoryProgress.trans {R : Finset ℕ} {before middle after : State}
    (first : MemoryProgress R before middle) (later : MemoryProgress R middle after) :
    MemoryProgress R before after := ⟨first.1.trans later.1, first.2.trans later.2⟩

theorem MemoryProgress.with_pc {R : Finset ℕ} {before after : State}
    (h : MemoryProgress R before after) (pc : ℕ) : MemoryProgress R before {after with pc := pc} := h

theorem progress_of_write (R : Finset ℕ) (before after : State) (target : ℕ) (value : Cell)
    (inside : target ∈ R) (heap : after.heap = Function.update before.heap target value)
    (live : after.live = insert target before.live) : MemoryProgress R before after := by
  have different (query : ℕ) (outside : query ∉ R) : query ≠ target := by
    intro same
    exact outside (same.symm ▸ inside)
  constructor
  · constructor
    · intro query outside
      rw [heap]
      exact Function.update_of_ne (different query outside) _ _
    · intro query outside
      rw [live]
      simp only [Finset.mem_insert, different query outside, false_or]
  · rw [live]
    exact Finset.subset_insert _ _

def NoMemoryWrite : Instruction → Prop
  | .store _ _ | .release _ => False
  | _ => True

theorem execute_no_memory_write (R : Finset ℕ) (input : List Cell) (instruction : Instruction)
    (before after : State) (clean : NoMemoryWrite instruction)
    (executed : instruction.execute input before = some after) : MemoryProgress R before after := by
  have safe : WritesWithin ∅ instruction before := by
    cases instruction <;> simp_all [NoMemoryWrite, WritesWithin]
  have emptyFrame := execute_memoryFrame ∅ instruction input before after safe executed
  constructor
  · exact ⟨fun address _ => emptyFrame.1 address (Finset.notMem_empty _),
      fun address _ => emptyFrame.2 address (Finset.notMem_empty _)⟩
  · intro address member
    exact (emptyFrame.2 address (Finset.notMem_empty _)).mpr member

theorem linearExecute_no_memory_write (R : Finset ℕ) (input : List Cell) (code : List Instruction)
    (before after : State) (clean : ∀ instruction ∈ code, NoMemoryWrite instruction)
    (executed : linearExecute input code before = some after) : MemoryProgress R before after := by
  induction code generalizing before with
  | nil =>
      have same : before = after := Option.some.inj executed
      subst after
      exact MemoryProgress.refl R before
  | cons instruction rest ih =>
      obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp executed
      exact (execute_no_memory_write R input instruction before middle (clean instruction (by simp)) first).trans
        (ih middle (fun other member => clean other (by simp only [List.mem_cons]; exact Or.inr member)) later)

/-- All slot commands have one store, at their final literal instruction. -/
theorem command_early_no_memory_write (command : SlotCommand) (count : ℕ)
    (short : count < command.code.length) :
    ∀ instruction ∈ command.code.take count, NoMemoryWrite instruction := by
  cases command with
  | constant target value =>
      change count < 4 at short
      interval_cases count <;> simp [SlotCommand.code, PDCompute.Solver.constantSlot, storeSlot, NoMemoryWrite]
  | copy source target =>
      change count < 6 at short
      interval_cases count <;> simp [SlotCommand.code, PDCompute.Solver.copySlot, loadSlot, storeSlot, NoMemoryWrite]
  | natural operation left right target =>
      change count < 10 at short
      interval_cases count <;> simp [SlotCommand.code, natBinarySlots, loadSlot, storeSlot, NoMemoryWrite]
  | rational operation left right target =>
      change count < 10 at short
      interval_cases count <;> simp [SlotCommand.code, PDCompute.Solver.ratBinarySlots, loadSlot, storeSlot, NoMemoryWrite]
  | toRational source target =>
      change count < 7 at short
      interval_cases count <;> simp [SlotCommand.code, natToRatSlot, loadSlot, storeSlot, NoMemoryWrite]

def LinearPrefixMemory (R : Finset ℕ) (input : List Cell) (code : List Instruction) (before : State) : Prop :=
  ∀ count after, linearExecute input (code.take count) before = some after → MemoryProgress R before after

theorem LinearPrefixMemory.final {R : Finset ℕ} {input : List Cell} {code : List Instruction}
    {before after : State} (h : LinearPrefixMemory R input code before)
    (executed : linearExecute input code before = some after) : MemoryProgress R before after := by
  apply h code.length after
  simpa only [List.take_length] using executed

theorem LinearPrefixMemory.append (R : Finset ℕ) (input : List Cell)
    (first later : List Instruction) (before middle : State)
    (executed : linearExecute input first before = some middle)
    (hfirst : LinearPrefixMemory R input first before) (hlater : LinearPrefixMemory R input later middle) :
    LinearPrefixMemory R input (first ++ later) before := by
  intro count after actual
  by_cases short : count ≤ first.length
  · rw [List.take_append_of_le_length short] at actual
    exact hfirst count after actual
  · rw [List.take_append, List.take_of_length_le (by omega : first.length ≤ count),
      linearExecute_append, executed, Option.bind_some] at actual
    exact (hfirst.final executed).trans (hlater (count - first.length) after actual)

theorem command_prefix_memory (R : Finset ℕ) (command : SlotCommand) (input : List Cell)
    (before : State) (memory next : SlotMemory) (matched : MemoryMatch before memory)
    (evaluated : command.eval memory = some next) (inside : Memory.target command ∈ R) :
    LinearPrefixMemory R input command.code before := by
  obtain ⟨terminal, executed, matchAfter, _, _⟩ := command.realize input before memory next matched evaluated
  obtain ⟨value, same⟩ := Memory.eval_is_write command memory next evaluated
  have frame : MemoryProgress R before terminal := by
    apply progress_of_write R before terminal (Memory.target command) value inside
    · rw [matchAfter.heap, same]
      change Function.update memory.value (Memory.target command) value = _
      rw [matched.heap]
    · rw [matchAfter.live, same]
      change insert (Memory.target command) memory.present = _
      rw [matched.live]
  intro count after actual
  by_cases short : count < command.code.length
  · exact linearExecute_no_memory_write R input (command.code.take count) before after
      (command_early_no_memory_write command count short) actual
  · rw [List.take_of_length_le (by omega : command.code.length ≤ count)] at actual
    have equal : after = terminal := Option.some.inj (actual.symm.trans executed)
    subst after
    exact frame

theorem sequence_prefix_memory (R : Finset ℕ) (commands : List SlotCommand) (input : List Cell)
    (before : State) (memory next : SlotMemory) (matched : MemoryMatch before memory)
    (evaluated : slotSequenceEval commands memory = some next)
    (inside : ∀ command ∈ commands, Memory.target command ∈ R) :
    LinearPrefixMemory R input (slotSequenceCode commands) before := by
  induction commands generalizing before memory with
  | nil =>
      intro count after actual
      have same : before = after := Option.some.inj (by simpa [slotSequenceCode, linearExecute] using actual)
      subst after
      exact MemoryProgress.refl R before
  | cons command rest ih =>
      obtain ⟨middleMemory, firstEval, laterEval⟩ := Option.bind_eq_some_iff.mp evaluated
      have first := command_prefix_memory R command input before memory middleMemory matched firstEval
        (inside command (by simp))
      obtain ⟨middle, executed, matchMiddle, _, _⟩ := command.realize input before memory middleMemory matched firstEval
      have later := ih middle middleMemory matchMiddle laterEval
        (fun other member => inside other (by simp only [List.mem_cons]; exact Or.inr member))
      simpa only [slotSequenceCode, List.flatMap_cons] using
        LinearPrefixMemory.append R input command.code (slotSequenceCode rest) before middle executed first later

end PDROC.D27Prepare.Q
