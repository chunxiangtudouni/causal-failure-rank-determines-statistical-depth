module

public import Paid.PDROC_BitVM_Log_InputLoad_069

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.InputLoad

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Uniform actual-word cost for this one opcode. The finite search has at
most13 static candidates, but old work and destination words are still
charged. This is not an assumed input-only bound on arbitrary old scratch. -/

theorem input_cell_length (input : List Cell) (query : ℕ) (value : Cell)
    (found : input[query]? = some value) :
    (encodeCellBits value).length ≤ (encodeBits input).length := by
  have payload : ∀ (cells : List Cell) (index : ℕ), cells[index]? = some value →
      (encodeCellBits value).length ≤ (cells.flatMap encodeCellBits).length := by
    intro cells
    induction cells with
    | nil => intro index answer; simp at answer
    | cons cell rest ih =>
      intro index answer
      cases index with
      | zero =>
        have same : cell = value := Option.some.inj answer
        subst cell
        simp only [List.flatMap_cons, List.length_append]
        omega
      | succ index =>
        have bound := ih index answer
        simp only [List.flatMap_cons, List.length_append]
        omega
  have bound := payload input query found
  simp only [encodeBits, List.length_append, List.length_cons, List.length_nil]
  omega

def opcodeBudget (input : List Cell) (ram : RAMState) (pointer destination : Register)
    (contents : Stack → List Bool) :=
  6 * (workCap contents + 3) + 3 * (encodeCellBits (ram.register pointer)).length +
    (encodeCellBits (ram.register destination)).length + 2 * (encodeBits input).length + 1000

theorem load_step_bounded (core : Bool) (input : List Cell) (ram next : RAMState)
    (pointer destination : Register) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (size : input.length = BankMount.fieldCount core) (bank : BankAt input before.stk)
    (executed : Instruction.execute input (.loadInput destination pointer) ram = some next) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = true ∧ RegistersRepresent next after ∧ BankAt input after.stk ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → index ≠ registerSlot destination →
        after.stk index = before.stk index) ∧
      run.length ≤ opcodeBudget input ram pointer destination before.stk := by
  obtain ⟨query, value, run, after, pointerValue, answer, nextValue, head, chain, last, halt,
      done, flag, registers, banks, frame, length⟩ :=
    load_step_refinement core input ram next pointer destination before position represented size bank executed
  refine ⟨run, after, head, chain, last, halt, done, flag, registers, banks, frame, ?_⟩
  have queryBound : query < 13 := by
    have inside : query < input.length := by
      by_contra missing
      have absent : input[query]? = none := List.getElem?_eq_none (by omega)
      rw [answer] at absent
      cases absent
    have fields := BankMount.fieldCount_le core
    omega
  have pointerLength : (encodeNatBits query).length ≤ (encodeCellBits (ram.register pointer)).length := by
    simp only [pointerValue, encodeCellBits, List.length_cons]
    omega
  have cellLength := input_cell_length input query value answer
  have clearEqual : clearBudget before.stk = 6 * (workCap before.stk + 3) + 1 := rfl
  simp only [selectionBudget] at length
  rw [clearEqual] at length
  unfold opcodeBudget
  omega

theorem load_failure_bounded (core : Bool) (input : List Cell) (ram : RAMState)
    (pointer destination : Register) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (size : input.length = BankMount.fieldCount core) (bank : BankAt input before.stk)
    (executed : Instruction.execute input (.loadInput destination pointer) ram = none) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = false ∧ RegistersRepresent ram after ∧ BankAt input after.stk ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → after.stk index = before.stk index) ∧
      run.length ≤ opcodeBudget input ram pointer destination before.stk := by
  cases pointerValue : ram.register pointer with
  | rational value =>
    obtain ⟨run, after, head, chain, last, halt, done, flag, sourceExecute, registers, banks, frame, length⟩ :=
      load_rational_refinement core input ram pointer destination value before position represented bank pointerValue
    refine ⟨run, after, head, chain, last, halt, done, flag, registers, banks, frame, ?_⟩
    have clearEqual : clearBudget before.stk = 6 * (workCap before.stk + 3) + 1 := rfl
    rw [clearEqual] at length
    unfold opcodeBudget
    omega
  | natural query =>
    obtain ⟨run, after, head, chain, last, halt, done, flag, registers, banks, frame, length⟩ :=
      load_failure_refinement core input ram pointer destination before position represented size bank executed
    refine ⟨run, after, head, chain, last, halt, done, flag, registers, banks, frame, ?_⟩
    have pointerLength : (encodeNatBits query).length ≤ (encodeCellBits (ram.register pointer)).length := by
      simp only [pointerValue, encodeCellBits, List.length_cons]
      omega
    have fields := BankMount.fieldCount_le core
    have clearEqual : clearBudget before.stk = 6 * (workCap before.stk + 3) + 1 := rfl
    simp only [pointerValue, Cell.nat?, Option.getD_some, absentBudget] at length
    rw [clearEqual] at length
    unfold opcodeBudget
    omega

end PDROC.BitVM.Log.InputLoad
