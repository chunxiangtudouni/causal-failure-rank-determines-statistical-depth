module

public import Paid.PDROC_BitVM_Log_HeapStore_030

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2100000

@[expose] public section

namespace PDROC.BitVM.Log.HeapStore

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev RAMState := PaperProofs.Paid.Computation.State

def ramStored (ram : RAMState) (address : ℕ) (valueSource : Register) : RAMState :=
  { Log.storeState ram address (ram.register valueSource) with pc := ram.pc + 1 }

theorem execute_store_nat (input : List Cell) (ram : RAMState) (pointer valueSource : Register) (address : ℕ)
    (natural : ram.register pointer = .natural address) :
    Instruction.execute input (.store pointer valueSource) ram = some (ramStored ram address valueSource) := by
  simp [Instruction.execute, natural, Cell.nat?, ramStored, Log.storeState]

theorem execute_store_rat (input : List Cell) (ram : RAMState) (pointer valueSource : Register) (value : ℚ)
    (rational : ram.register pointer = .rational value) :
    Instruction.execute input (.store pointer valueSource) ram = none := by
  simp [Instruction.execute, rational, Cell.nat?]

theorem stored_register (address : ℕ) (valueSource : Register) (contents : Stack → List Bool) (reg : Register) :
    stored address valueSource contents (registerSlot reg) = contents (registerSlot reg) := by
  cases reg <;> simp [stored, cleaned, cleared25, cleared24, registerSlot,
    PaperProofs.Structure.LaminarTree.IndexedRAM.Register.word]

theorem stored_other (address : ℕ) (valueSource : Register) (contents : Stack → List Bool) (index : Stack)
    (not21 : index ≠ 21) (not24 : index ≠ 24) (not25 : index ≠ 25) (not26 : index ≠ 26) (not28 : index ≠ 28) :
    stored address valueSource contents index = contents index := by
  rw [stored, Function.update_of_ne not21, Function.update_of_ne not28]
  exact cleaned_outside contents index not24 not25 not26

/-- ONE real store trace obtains BOTH address and value from the represented
registers, preserves those registers and prepends the exact canonical event.
Neither the address word nor an encoded Cell is an external producer oracle. -/
theorem store_natural_refinement (input : List Cell) (ram : RAMState) (events : List HeapEvent)
    (pointer valueSource : Register) (address : ℕ) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (history : before.stk 21 = encodeHistory events) (refines : Refines events ram)
    (natural : ram.register pointer = .natural address) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program pointer valueSource) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer valueSource) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = true ∧
      Instruction.execute input (.store pointer valueSource) ram = some (ramStored ram address valueSource) ∧
      Refines (events ++ [⟨address, some (ram.register valueSource)⟩]) (ramStored ram address valueSource) ∧
      RegistersRepresent (ramStored ram address valueSource) after ∧
      after.stk 21 = encodeHistory (events ++ [⟨address, some (ram.register valueSource)⟩]) ∧
      (∀ index : Stack, index ≠ 21 → index ≠ 24 → index ≠ 25 → index ≠ 26 → index ≠ 28 → after.stk index = before.stk index) ∧
      run.length ≤ clearBudget before.stk + (before.stk 28).length +
        50 * ((encodeNatBits address).length + (encodeCellBits (ram.register valueSource)).length + 1) := by
  have actualRegister : before.stk (registerSlot pointer) = encodeCellBits (.natural address) := by
    simpa only [natural] using represented pointer
  obtain ⟨run, after, head, chain, last, halt, done, saved, data, length⟩ :=
    natural_runs pointer valueSource address before.stk before.var actualRegister
  have headBefore : run.head? = some before := by
    rcases before with ⟨label, vars, contents⟩
    change label = some startLabel at position
    subst label
    exact head
  have updated : Refines (events ++ [⟨address, some (ram.register valueSource)⟩]) (ramStored ram address valueSource) :=
    refines.store address (ram.register valueSource)
  refine ⟨run, after, headBefore, chain, last, halt, done, ?_, execute_store_nat input ram pointer valueSource address natural,
    updated, ?_, ?_, ?_, ?_⟩
  · rw [saved]; rfl
  · intro reg
    rw [data, stored_register]
    exact represented reg
  · rw [data]
    change true :: (encodeNatBits address ++ (before.stk (registerSlot valueSource) ++ before.stk 21)) =
      encodeHistory (events ++ [⟨address, some (ram.register valueSource)⟩])
    rw [represented valueSource, history, encodeHistory_append]
    simp only [encodeEvent, List.cons_append, List.append_assoc]
  · intro index not21 not24 not25 not26 not28
    rw [data]
    exact stored_other address valueSource before.stk index not21 not24 not25 not26 not28
  · simpa only [represented valueSource] using length

/-- Wrong pointer type follows the actual false branch without copying a
source Cell or writing a record. It agrees with original execute=None. -/
theorem store_rational_refinement (input : List Cell) (ram : RAMState) (events : List HeapEvent)
    (pointer valueSource : Register) (value : ℚ) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (history : before.stk 21 = encodeHistory events) (rational : ram.register pointer = .rational value) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program pointer valueSource) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer valueSource) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = false ∧
      Instruction.execute input (.store pointer valueSource) ram = none ∧ RegistersRepresent ram after ∧
      after.stk 21 = encodeHistory events ∧
      (∀ index : Stack, index ≠ 24 → index ≠ 25 → index ≠ 26 → after.stk index = before.stk index) ∧
      run.length ≤ clearBudget before.stk + 5 := by
  have actualRegister : before.stk (registerSlot pointer) = encodeCellBits (.rational value) := by
    simpa only [rational] using represented pointer
  obtain ⟨run, after, head, chain, last, halt, done, saved, data, length⟩ :=
    rational_runs pointer valueSource value before.stk before.var actualRegister
  have headBefore : run.head? = some before := by
    rcases before with ⟨label, vars, contents⟩
    change label = some startLabel at position
    subst label
    exact head
  refine ⟨run, after, headBefore, chain, last, halt, done, ?_, execute_store_rat input ram pointer valueSource value rational,
    ?_, ?_, ?_, length⟩
  · rw [saved]; rfl
  · intro reg
    rw [data, cleaned_register]
    exact represented reg
  · rw [data, cleaned_outside before.stk 21 (by decide) (by decide) (by decide), history]
  · intro index not24 not25 not26
    rw [data]
    exact cleaned_outside before.stk index not24 not25 not26

end PDROC.BitVM.Log.HeapStore
