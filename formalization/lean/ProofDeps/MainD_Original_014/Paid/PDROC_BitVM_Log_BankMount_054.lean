module

public import Paid.PDROC_BitVM_Log_BankMount_053

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.BankMount

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native

/-! ONE complete selected mount path: real clears/header/fields/footer/
cleanup/HALT. Its source input is the actual forward encodeBits list already
on stack0, with arbitrary caller suffix. No free readonly-bank substitution.
The raw cost keeps actual old bank/work lengths, never a P-only scratch bound. -/

def mountBudget (core : Bool) (cells : List Cell) (contents : Stack → List Bool) :=
  readyBudget core cells contents + (encodeNatBits (fieldCount core)).length +
    (cells.flatMap encodeCellBits).length + 20

theorem source_runs (core : Bool) (cells : List Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (store : Store)
    (size : cells.length = fieldCount core) (input : contents 0 = encodeBits cells ++ suffix) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram core) after = none ∧ after.l = none ∧
      Query.equality after.var.1.2.1 = true ∧ Mounted contents cells suffix after.stk ∧
      run.length ≤ mountBudget core cells contents := by
  obtain ⟨left, vars, data, leftHead, leftChain, leftLast, savedNat, savedExtra, ready, leftLength⟩ :=
    ready_runs core cells suffix contents store size input
  obtain ⟨right, after, rightHead, rightChain, rightLast, halt, done, flag, mounted, rightPositive, rightLength⟩ :=
    finish_runs core contents cells suffix data vars ready
  let middle : SourceState := ⟨some footerLabel, (vars, ()), data⟩
  let run := left ++ right.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, leftHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) :=
    TwoStack.join_chain left right middle leftChain rightChain leftLast rightHead
  have notOne : right.length ≠ 1 := by omega
  have last : run.getLast? = some after := by
    simp only [run, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte, rightLast, Option.some_or]
  refine ⟨run, after, head, chain, last, halt, done, flag, mounted, ?_⟩
  have archiveLength : (data 25).length = (encodeNatBits (fieldCount core)).length + (cells.flatMap encodeCellBits).length := by
    rw [ready.archive]
    simp only [List.length_reverse, List.length_append]
  rw [archiveLength] at rightLength
  simp only [run, List.length_append, List.length_tail, mountBudget]
  omega

/-- Complete physical prepare6/core13 input mount, with no initialized bank,
no empty old work and no extra fields required from its whole caller.
Only the actual encoded input and the original fixed field count are given. -/
theorem runs (core : Bool) (cells : List Cell) (suffix : List Bool) (before : State)
    (position : before.l = some startLabel) (size : cells.length = fieldCount core)
    (input : before.stk 0 = encodeBits cells ++ suffix) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program core) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = true ∧ Mounted before.stk cells suffix after.stk ∧
      run.length ≤ mountBudget core cells before.stk := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceFlag, sourceMounted, sourceLength⟩ :=
    source_runs core cells suffix before.stk before.var size input
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace HeapLoad.storeIso (sourceProgram core) source
      (⟨some startLabel, (before.var, ()), before.stk⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  have headBefore : run.head? = some before := by
    rcases before with ⟨currentLabel, currentVar, currentData⟩
    change currentLabel = some startLabel at position
    subst currentLabel
    exact head
  refine ⟨run, after, headBefore, chain, last, halt, label.trans sourceDone, ?_, ?_, ?_⟩
  · rw [saved]; exact sourceFlag
  · rw [data]; exact sourceMounted
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.BankMount
