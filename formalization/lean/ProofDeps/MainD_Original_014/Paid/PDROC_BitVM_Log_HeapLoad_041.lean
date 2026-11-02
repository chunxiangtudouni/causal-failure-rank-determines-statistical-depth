module

public import Paid.PDROC_BitVM_Log_HeapLoad_040

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.Log.HeapLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev RAMState := PaperProofs.Paid.Computation.State

def ramLoaded (ram : RAMState) (destination : Register) (value : Cell) : RAMState :=
  ({ ram with pc := ram.pc + 1 }).set destination value

theorem committed_register (destination reg : Register) (contents : Stack → List Bool) :
    committed destination contents (registerSlot reg) =
      if reg = destination then contents 28 else contents (registerSlot reg) := by
  have bounds := registerSlot_bounds reg
  have not26 : registerSlot reg ≠ 26 := by
    intro equal
    have values := congrArg Fin.val equal
    change (registerSlot reg).val = 26 at values
    omega
  have not28 : registerSlot reg ≠ 28 := by
    intro equal
    have values := congrArg Fin.val equal
    change (registerSlot reg).val = 28 at values
    omega
  rw [committed, Function.update_of_ne not28, clearedQuery, Function.update_of_ne not26, copiedResult]
  by_cases same : reg = destination
  · subst reg; simp only [Function.update_self, ↓reduceIte]
  · have different : registerSlot reg ≠ registerSlot destination := fun equal => same (registerSlot_injective equal)
    simp only [Function.update_of_ne different, same, ↓reduceIte]

theorem looked_outside (events : List HeapEvent) (query : ℕ) (contents : Stack → List Bool) (index : Stack)
    (outside : index.val < 24 ∨ 30 ≤ index.val) : looked events query contents index = contents index := by
  have not26 : index ≠ 26 := by intro equal; subst index; norm_num at outside
  have not28 : index ≠ 28 := by intro equal; subst index; norm_num at outside
  rw [looked, Function.update_of_ne not28, marshalled, Function.update_of_ne not26]
  exact preCleared_outside contents index outside

theorem committed_outside (destination : Register) (contents : Stack → List Bool) (index : Stack)
    (notDestination : index ≠ registerSlot destination) (not26 : index ≠ 26) (not28 : index ≠ 28) :
    committed destination contents index = contents index := by
  simp only [committed, clearedQuery, copiedResult, Function.update_of_ne not28,
    Function.update_of_ne not26, Function.update_of_ne notDestination]

/-- A successful original RAM load, with simultaneous true Bool execution,
logical register commit, unchanged live heap/history and exact caller frame.
The read Cell is the actual latest live value; old default Nat0 never suffices. -/
theorem load_found_refinement (input : List Cell) (ram : RAMState) (events : List HeapEvent)
    (pointer destination : Register) (query : ℕ) (value : Cell) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (history : before.stk 21 = encodeHistory events) (refines : Refines events ram)
    (natural : ram.register pointer = .natural query) (found : lookup events query = some value) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer destination) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = true ∧
      Instruction.execute input (.load destination pointer) ram = some (ramLoaded ram destination value) ∧
      Refines events (ramLoaded ram destination value) ∧ RegistersRepresent (ramLoaded ram destination value) after ∧
      after.stk 21 = encodeHistory events ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → index ≠ registerSlot destination →
        after.stk index = before.stk index) ∧
      run.length ≤ foundBudget events query destination value before.stk := by
  have actualRegister : before.stk (registerSlot pointer) = encodeCellBits (.natural query) := by
    simpa only [natural] using represented pointer
  obtain ⟨run, after, head, chain, last, halt, done, flag, data, length⟩ :=
    found_runs pointer destination events query value before.stk before.var actualRegister history found
  have headBefore : run.head? = some before := by
    rcases before with ⟨label, vars, contents⟩
    change label = some startLabel at position
    subst label
    exact head
  have actualExecute : Instruction.execute input (.load destination pointer) ram = some (ramLoaded ram destination value) := by
    simpa only [found, Option.map_some, ramLoaded] using
      Lookup.execute_load_from_history input events ram destination pointer query refines natural
  refine ⟨run, after, headBefore, chain, last, halt, done, flag, actualExecute, refines, ?_, ?_, ?_, length⟩
  · intro reg
    rw [data, committed_register]
    by_cases same : reg = destination
    · subst reg
      rw [ite_eq_left rfl, (looked_fields events query before.stk).2.2, found]
      simp only [Lookup.valueBytes, ramLoaded, PaperProofs.Paid.Computation.State.set, Function.update_self]
    · rw [ite_eq_right same, looked_register]
      simpa only [ramLoaded, PaperProofs.Paid.Computation.State.set, Function.update_of_ne same] using represented reg
  · rw [data]
    cases destination <;> simp [committed, clearedQuery, copiedResult, looked, marshalled, preCleared,
      registerSlot, PaperProofs.Structure.LaminarTree.IndexedRAM.Register.word, history]
  · intro index outside notDestination
    have not26 : index ≠ 26 := by intro equal; subst index; norm_num at outside
    have not28 : index ≠ 28 := by intro equal; subst index; norm_num at outside
    rw [data, committed_outside destination _ index notDestination not26 not28]
    exact looked_outside events query before.stk index outside

/-- Absent and latest-tombstoned addresses both take the genuine failure
branch, preserve all registers and heap bytes, and agree with execute=None. -/
theorem load_missing_refinement (input : List Cell) (ram : RAMState) (events : List HeapEvent)
    (pointer destination : Register) (query : ℕ) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (history : before.stk 21 = encodeHistory events) (refines : Refines events ram)
    (natural : ram.register pointer = .natural query) (missing : lookup events query = none) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer destination) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = false ∧
      Instruction.execute input (.load destination pointer) ram = none ∧ RegistersRepresent ram after ∧
      after.stk 21 = encodeHistory events ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → after.stk index = before.stk index) ∧
      run.length ≤ queryBudget events query before.stk + 2 := by
  have actualRegister : before.stk (registerSlot pointer) = encodeCellBits (.natural query) := by
    simpa only [natural] using represented pointer
  obtain ⟨run, after, head, chain, last, halt, done, flag, data, length⟩ :=
    missing_runs pointer destination events query before.stk before.var actualRegister history missing
  have headBefore : run.head? = some before := by
    rcases before with ⟨label, vars, contents⟩
    change label = some startLabel at position
    subst label
    exact head
  have actualExecute : Instruction.execute input (.load destination pointer) ram = none := by
    simpa only [missing, Option.map_none] using
      Lookup.execute_load_from_history input events ram destination pointer query refines natural
  refine ⟨run, after, headBefore, chain, last, halt, done, flag, actualExecute, ?_, ?_, ?_, length⟩
  · intro reg
    rw [data, looked_register]
    exact represented reg
  · rw [data, looked_outside events query before.stk 21 (by decide)]
    exact history
  · intro index outside
    rw [data]
    exact looked_outside events query before.stk index outside

/-- A rational pointer cannot be a heap address. Actual clear/type-failure
execution preserves registers/history and agrees with original load=None. -/
theorem load_rational_refinement (input : List Cell) (ram : RAMState) (events : List HeapEvent)
    (pointer destination : Register) (value : ℚ) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (history : before.stk 21 = encodeHistory events) (rational : ram.register pointer = .rational value) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer destination) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = false ∧
      Instruction.execute input (.load destination pointer) ram = none ∧ RegistersRepresent ram after ∧
      after.stk 21 = encodeHistory events ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → after.stk index = before.stk index) ∧
      run.length ≤ clearBudget before.stk + 5 := by
  have actualRegister : before.stk (registerSlot pointer) = encodeCellBits (.rational value) := by
    simpa only [rational] using represented pointer
  obtain ⟨run, after, head, chain, last, halt, done, flag, data, length⟩ :=
    rational_runs pointer destination value before.stk before.var actualRegister
  have headBefore : run.head? = some before := by
    rcases before with ⟨label, vars, contents⟩
    change label = some startLabel at position
    subst label
    exact head
  have actualExecute : Instruction.execute input (.load destination pointer) ram = none := by
    simp [Instruction.execute, rational, Cell.nat?]
  refine ⟨run, after, headBefore, chain, last, halt, done, flag, actualExecute, ?_, ?_, ?_, length⟩
  · intro reg
    rw [data, preCleared_register]
    exact represented reg
  · rw [data, preCleared_outside before.stk 21 (by decide)]
    exact history
  · intro index outside
    rw [data]
    exact preCleared_outside before.stk index outside

end PDROC.BitVM.Log.HeapLoad
