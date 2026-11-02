module

public import Paid.PDROC_BitVM_Log_InputLoad_068

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.InputLoad

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Original source failure and source-step adapters. The source execute
premise determines its own pointer and selected Cell. No success answer,
host bank indexing or caller-empty workspace is supplied to the machine. -/

theorem execute_input_eq (input : List Cell) (ram : RAMState) (pointer destination : Register) (query : ℕ)
    (natural : ram.register pointer = .natural query) :
    Instruction.execute input (.loadInput destination pointer) ram =
      input[query]?.map (ramLoaded ram destination) := by
  cases answer : input[query]? <;> simp [Instruction.execute, natural, Cell.nat?, answer, ramLoaded]
  rfl

theorem load_missing_refinement (core : Bool) (input : List Cell) (ram : RAMState)
    (pointer destination : Register) (query : ℕ) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (size : input.length = BankMount.fieldCount core) (bank : BankAt input before.stk)
    (natural : ram.register pointer = .natural query) (missing : input[query]? = none) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = false ∧
      Instruction.execute input (.loadInput destination pointer) ram = none ∧
      RegistersRepresent ram after ∧ BankAt input after.stk ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → after.stk index = before.stk index) ∧
      run.length ≤ absentBudget core query before.stk := by
  have outside : input.length ≤ query := List.getElem?_eq_none_iff.mp missing
  have range : BankMount.fieldCount core ≤ query := by omega
  have actualRegister : before.stk (registerSlot pointer) = encodeCellBits (.natural query) := by
    simpa only [natural] using represented pointer
  obtain ⟨run, after, head, chain, last, halt, done, flag, data, length⟩ :=
    absent_runs core pointer destination query before.stk before.var actualRegister range
  have headBefore : run.head? = some before := by
    rcases before with ⟨label, vars, contents⟩
    change label = some startLabel at position
    subst label
    exact head
  have executed : Instruction.execute input (.loadInput destination pointer) ram = none := by
    rw [execute_input_eq input ram pointer destination query natural, missing, Option.map_none]
  refine ⟨run, after, headBefore, chain, last, halt, done, flag, executed, ?_, ?_, ?_, length⟩
  · intro reg
    rw [data, marshalled_register]
    exact represented reg
  · intro field
    rw [data, marshalled_bank]
    exact bank field
  · intro index bound
    rw [data]
    exact marshalled_outside query before.stk index bound

theorem load_rational_refinement (core : Bool) (input : List Cell) (ram : RAMState)
    (pointer destination : Register) (value : ℚ) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (bank : BankAt input before.stk) (rational : ram.register pointer = .rational value) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = false ∧
      Instruction.execute input (.loadInput destination pointer) ram = none ∧
      RegistersRepresent ram after ∧ BankAt input after.stk ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → after.stk index = before.stk index) ∧
      run.length ≤ clearBudget before.stk + 5 := by
  have actualRegister : before.stk (registerSlot pointer) = encodeCellBits (.rational value) := by
    simpa only [rational] using represented pointer
  obtain ⟨run, after, head, chain, last, halt, done, flag, data, length⟩ :=
    rational_runs core pointer destination value before.stk before.var actualRegister
  have headBefore : run.head? = some before := by
    rcases before with ⟨label, vars, contents⟩
    change label = some startLabel at position
    subst label
    exact head
  have executed : Instruction.execute input (.loadInput destination pointer) ram = none := by
    simp [Instruction.execute, rational, Cell.nat?]
  refine ⟨run, after, headBefore, chain, last, halt, done, flag, executed, ?_, ?_, ?_, length⟩
  · intro reg
    rw [data]
    change HeapLoad.preCleared 6 before.stk (registerSlot reg) = _
    rw [HeapLoad.preCleared_register]
    exact represented reg
  · intro field
    have outside : (BankDrain.bankSlot field).val < 24 := by
      change field.val + 1 < 24
      omega
    rw [data]
    change HeapLoad.preCleared 6 before.stk (BankDrain.bankSlot field) = _
    rw [HeapLoad.preCleared_outside before.stk (BankDrain.bankSlot field) (Or.inl outside)]
    exact bank field
  · intro index bound
    rw [data]
    exact HeapLoad.preCleared_outside before.stk index bound

/-- The original successful step itself supplies the real address and Cell.
All semantics, flags, bank preservation and cost refer to ONE actual path. -/
theorem load_step_refinement (core : Bool) (input : List Cell) (ram next : RAMState)
    (pointer destination : Register) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (size : input.length = BankMount.fieldCount core) (bank : BankAt input before.stk)
    (executed : Instruction.execute input (.loadInput destination pointer) ram = some next) :
    ∃ (query : ℕ) (value : Cell) (run : List State) (after : State),
      ram.register pointer = .natural query ∧ input[query]? = some value ∧ next = ramLoaded ram destination value ∧
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = true ∧ RegistersRepresent next after ∧ BankAt input after.stk ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → index ≠ registerSlot destination →
        after.stk index = before.stk index) ∧
      run.length ≤ selectionBudget query before.stk + (encodeCellBits (ram.register destination)).length +
        2 * (encodeCellBits value).length + (encodeNatBits query).length + 12 := by
  cases pointerValue : ram.register pointer with
  | rational value => simp [Instruction.execute, pointerValue, Cell.nat?] at executed
  | natural query =>
    rw [execute_input_eq input ram pointer destination query pointerValue] at executed
    cases answer : input[query]? with
    | none => simp only [answer, Option.map_none, reduceCtorEq] at executed
    | some value =>
      have nextValue : next = ramLoaded ram destination value := by
        simpa only [answer, Option.map_some, Option.some.injEq] using executed.symm
      subst next
      obtain ⟨run, after, head, chain, last, halt, done, flag, sourceExecute, registers, banks, frame, length⟩ :=
        load_found_refinement core input ram pointer destination query value before position represented size bank pointerValue answer
      exact ⟨query, value, run, after, rfl, answer, rfl, head, chain, last, halt, done, flag,
        registers, banks, frame, length⟩

theorem load_failure_refinement (core : Bool) (input : List Cell) (ram : RAMState)
    (pointer destination : Register) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (size : input.length = BankMount.fieldCount core) (bank : BankAt input before.stk)
    (executed : Instruction.execute input (.loadInput destination pointer) ram = none) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = false ∧ RegistersRepresent ram after ∧ BankAt input after.stk ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → after.stk index = before.stk index) ∧
      run.length ≤ absentBudget core ((ram.register pointer).nat?.getD 0) before.stk := by
  cases pointerValue : ram.register pointer with
  | rational value =>
    obtain ⟨run, after, head, chain, last, halt, done, flag, sourceExecute, registers, banks, frame, length⟩ :=
      load_rational_refinement core input ram pointer destination value before position represented bank pointerValue
    refine ⟨run, after, head, chain, last, halt, done, flag, registers, banks, frame, ?_⟩
    simp only [Cell.nat?, Option.getD_none, absentBudget]
    omega
  | natural query =>
    rw [execute_input_eq input ram pointer destination query pointerValue] at executed
    have missing : input[query]? = none := by
      cases answer : input[query]? with
      | none => rfl
      | some value => simp only [answer, Option.map_some, reduceCtorEq] at executed
    obtain ⟨run, after, head, chain, last, halt, done, flag, sourceExecute, registers, banks, frame, length⟩ :=
      load_missing_refinement core input ram pointer destination query before position represented size bank pointerValue missing
    refine ⟨run, after, head, chain, last, halt, done, flag, registers, banks, frame, ?_⟩
    simpa only [pointerValue, Cell.nat?, Option.getD_some] using length

end PDROC.BitVM.Log.InputLoad
