module

public import Paid.PDROC_BitVM_Log_HeapRelease_023

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.Log.HeapRelease

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev RAMState := PaperProofs.Paid.Computation.State

def ramReleased (ram : RAMState) (address : ℕ) : RAMState :=
  { Log.releaseState ram address with pc := ram.pc + 1 }

theorem execute_release_nat (input : List Cell) (ram : RAMState) (pointer : Register) (address : ℕ)
    (natural : ram.register pointer = .natural address) :
    Instruction.execute input (.release pointer) ram = some (ramReleased ram address) := by
  simp [Instruction.execute, natural, Cell.nat?, ramReleased, Log.releaseState]

theorem execute_release_rat (input : List Cell) (ram : RAMState) (pointer : Register) (value : ℚ)
    (rational : ram.register pointer = .rational value) :
    Instruction.execute input (.release pointer) ram = none := by
  simp [Instruction.execute, rational, Cell.nat?]

theorem released_register (value : ℕ) (contents : Stack → List Bool) (reg : Register) :
    released value contents (registerSlot reg) = contents (registerSlot reg) := by
  cases reg <;> simp [released, cleaned, cleared25, cleared24, registerSlot,
    PaperProofs.Structure.LaminarTree.IndexedRAM.Register.word]

theorem released_other (value : ℕ) (contents : Stack → List Bool) (index : Stack)
    (not21 : index ≠ 21) (not24 : index ≠ 24) (not25 : index ≠ 25) (not26 : index ≠ 26) :
    released value contents index = contents index := by
  rw [released, Function.update_of_ne not21]
  exact cleaned_outside contents index not24 not25 not26

/-- ONE actual release path is tied to the original instruction semantics.
Its address comes from the actual register, not a supplied encoded address.
The logical Refines conclusion entails BOTH heapNat0 reset and live erasure. -/
theorem release_natural_refinement (input : List Cell) (ram : RAMState) (events : List HeapEvent)
    (pointer : Register) (address : ℕ) (before : State)
    (position : before.l = some startLabel)
    (represented : RegistersRepresent ram before)
    (history : before.stk 21 = encodeHistory events)
    (refines : Refines events ram) (natural : ram.register pointer = .natural address) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program pointer) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = true ∧
      Instruction.execute input (.release pointer) ram = some (ramReleased ram address) ∧
      Refines (events ++ [⟨address, none⟩]) (ramReleased ram address) ∧
      RegistersRepresent (ramReleased ram address) after ∧
      after.stk 21 = encodeHistory (events ++ [⟨address, none⟩]) ∧
      (∀ index : Stack, index ≠ 21 → index ≠ 24 → index ≠ 25 → index ≠ 26 → after.stk index = before.stk index) ∧
      run.length ≤ clearBudget before.stk + 30 * ((encodeNatBits address).length + 1) := by
  have actualRegister : before.stk (registerSlot pointer) = encodeCellBits (.natural address) := by
    simpa only [natural] using represented pointer
  obtain ⟨run, after, head, chain, last, halt, done, saved, data, length⟩ :=
    natural_runs pointer address before.stk before.var actualRegister
  have headBefore : run.head? = some before := by
    rcases before with ⟨label, vars, contents⟩
    change label = some startLabel at position
    subst label
    exact head
  have updatedRefines : Refines (events ++ [⟨address, none⟩]) (ramReleased ram address) := refines.release address
  refine ⟨run, after, headBefore, chain, last, halt, done, ?_, execute_release_nat input ram pointer address natural,
    updatedRefines, ?_, ?_, ?_, length⟩
  · rw [saved]; rfl
  · intro reg
    rw [data, released_register]
    exact represented reg
  · rw [data]
    change false :: (encodeNatBits address ++ before.stk 21) = encodeHistory (events ++ [⟨address, none⟩])
    rw [history, encodeHistory_append]
    rfl
  · intro index not21 not24 not25 not26
    rw [data]
    exact released_other address before.stk index not21 not24 not25 not26

/-- The actual Rat-pointer failure route preserves every logical RAM byte.
Only real scratch cleanup occurs. It agrees with official execute=None. -/
theorem release_rational_refinement (input : List Cell) (ram : RAMState) (events : List HeapEvent)
    (pointer : Register) (value : ℚ) (before : State)
    (position : before.l = some startLabel)
    (represented : RegistersRepresent ram before)
    (history : before.stk 21 = encodeHistory events)
    (rational : ram.register pointer = .rational value) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program pointer) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = false ∧
      Instruction.execute input (.release pointer) ram = none ∧ RegistersRepresent ram after ∧
      after.stk 21 = encodeHistory events ∧
      (∀ index : Stack, index ≠ 24 → index ≠ 25 → index ≠ 26 → after.stk index = before.stk index) ∧
      run.length ≤ clearBudget before.stk + 5 := by
  have actualRegister : before.stk (registerSlot pointer) = encodeCellBits (.rational value) := by
    simpa only [rational] using represented pointer
  obtain ⟨run, after, head, chain, last, halt, done, saved, data, length⟩ :=
    rational_runs pointer value before.stk before.var actualRegister
  have headBefore : run.head? = some before := by
    rcases before with ⟨label, vars, contents⟩
    change label = some startLabel at position
    subst label
    exact head
  refine ⟨run, after, headBefore, chain, last, halt, done, ?_, execute_release_rat input ram pointer value rational,
    ?_, ?_, ?_, length⟩
  · rw [saved]; rfl
  · intro reg
    rw [data, cleaned_register]
    exact represented reg
  · rw [data, cleaned_outside before.stk 21 (by decide) (by decide) (by decide), history]
  · intro index not24 not25 not26
    rw [data]
    exact cleaned_outside before.stk index not24 not25 not26

end PDROC.BitVM.Log.HeapRelease
