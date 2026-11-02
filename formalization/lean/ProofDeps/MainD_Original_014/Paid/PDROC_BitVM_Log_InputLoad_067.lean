module

public import Paid.PDROC_BitVM_Log_InputLoad_066

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.InputLoad

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal

/-! Actual wrong-type and out-of-range paths. They do not write a target
register and do not substitute a default Nat0 for a missing input cell. -/

def rationalResult (store : Store) := HeapPointer.setTyped (HeapPointer.saveTag (cleared store) (some true)) false

theorem source_rational_runs (core : Bool) (pointer destination : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram core pointer destination) after = none ∧
      after.l = none ∧ after.var = (rationalResult store, ()) ∧ after.stk = (preCleared 6 contents) ∧
      run.length ≤ clearBudget contents + 5 := by
  obtain ⟨readyTrace, readyHead, readyChain, readyLast, readyLength⟩ := rational_ready core pointer destination value contents store register
  let beforeBranch : SourceState := ⟨some typeBranch, (rationalResult store, ()), (preCleared 6 contents)⟩
  let invalid : SourceState := ⟨some invalidLabel, (rationalResult store, ()), (preCleared 6 contents)⟩
  let final : SourceState := ⟨none, (rationalResult store, ()), (preCleared 6 contents)⟩
  let tailTrace := [beforeBranch, invalid, final]
  have tailHead : tailTrace.head? = some beforeBranch := rfl
  have tailChain : tailTrace.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) := by
    apply List.isChain_cons_cons.mpr
    refine ⟨type_invalid core pointer destination (rationalResult store, ()) ((preCleared 6 contents)) rfl, ?_⟩
    exact List.isChain_cons_cons.mpr ⟨invalid_halt core pointer destination (rationalResult store, ()) ((preCleared 6 contents)), List.isChain_singleton _⟩
  let run := readyTrace ++ tailTrace.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, readyHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) :=
    TwoStack.join_chain readyTrace tailTrace beforeBranch readyChain tailChain readyLast tailHead
  have last : run.getLast? = some final := by
    simp only [run, tailTrace, List.tail_cons, List.getLast?_append, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.some_or]
  refine ⟨run, final, head, chain, last, rfl, rfl, rfl, rfl, ?_⟩
  simp only [run, tailTrace, List.tail_cons, List.length_append, List.length_cons, List.length_nil]
  omega

def absentBudget (core : Bool) (query : ℕ) (contents : Stack → List Bool) :=
  clearBudget contents + 2 * (encodeNatBits query).length + 50 * BankMount.fieldCount core + 20

theorem source_absent_runs (core : Bool) (pointer destination : Register) (query : ℕ)
    (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query))
    (range : BankMount.fieldCount core ≤ query) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.1.2.1 = false ∧ after.stk = marshalled query contents ∧
      run.length ≤ absentBudget core query contents := by
  obtain ⟨firstTrace, firstHead, firstChain, firstLast, firstLength⟩ := natural_ready core pointer destination query contents store register
  let pointerStore := pointerResult (cleared store)
  let pointerContents := marshalled query contents
  obtain ⟨scan, vars, scanHead, scanChain, scanLast, scanLength⟩ :=
    exhausted_runs core pointer destination query 0 range (by omega) pointerContents pointerStore (marshalled_ready query contents)
  have scanHeadExact : scan.head? = some (⟨some (literalLabel 0 InputLiteral.startLabel), (pointerStore, ()), pointerContents⟩ : SourceState) := by
    simpa only [candidateEntry, BankMount.fieldCount_pos core, ↓reduceDIte, Fin.mk_zero] using scanHead
  let boundary : SourceState := ⟨some typeBranch, (pointerStore, ()), pointerContents⟩
  let body := boundary :: scan
  have bodyHead : body.head? = some boundary := rfl
  have bodyChain : body.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) := by
    apply List.IsChain.cons scanChain
    intro next member
    rw [scanHeadExact] at member
    have equal := Option.mem_some_iff.mp member
    subst next
    exact type_step core pointer destination (pointerStore, ()) pointerContents rfl
  have bodyLast : body.getLast? = some (⟨some invalidLabel, (vars, ()), pointerContents⟩ : SourceState) := by
    simp only [body, List.getLast?_cons, scanLast, Option.getD_some]
  have scanPositive : 0 < scan.length := by
    cases scan with
    | nil => simp only [List.head?_nil, reduceCtorEq] at scanHead
    | cons first rest => simp only [List.length_cons]; omega
  have bodyNotOne : body.length ≠ 1 := by simp only [body, List.length_cons]; omega
  let left := firstTrace ++ body.tail
  have leftHead : left.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [left, List.head?_append, firstHead, Option.some_or]
  have leftChain : left.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) :=
    TwoStack.join_chain firstTrace body boundary firstChain bodyChain firstLast bodyHead
  have leftLast : left.getLast? = some (⟨some invalidLabel, (vars, ()), pointerContents⟩ : SourceState) := by
    simp only [left, List.getLast?_append, List.getLast?_tail, bodyNotOne, ↓reduceIte, bodyLast, Option.some_or]
  obtain ⟨right, after, rightHead, rightChain, rightLast, halt, done, flag, data, rightLength⟩ :=
    invalid_runs core pointer destination pointerContents vars
  let middle : SourceState := ⟨some invalidLabel, (vars, ()), pointerContents⟩
  let run := left ++ right.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, leftHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) :=
    TwoStack.join_chain left right middle leftChain rightChain leftLast rightHead
  have notOne : right.length ≠ 1 := by omega
  have last : run.getLast? = some after := by
    simp only [run, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte, rightLast, Option.some_or]
  refine ⟨run, after, head, chain, last, halt, done, flag, data, ?_⟩
  simp only [run, left, body, List.length_append, List.length_tail, List.length_cons, absentBudget]
  omega

theorem rational_runs (core : Bool) (pointer destination : Register) (value : ℚ)
    (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = false ∧ after.stk = preCleared 6 contents ∧ run.length ≤ clearBudget contents + 5 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    source_rational_runs core pointer destination value contents store register
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace HeapLoad.storeIso (sourceProgram core pointer destination) source
      (⟨some startLabel, (store, ()), contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved, sourceVar]; rfl
  · rw [length]; exact sourceLength

theorem absent_runs (core : Bool) (pointer destination : Register) (query : ℕ)
    (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query))
    (range : BankMount.fieldCount core ≤ query) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = false ∧ after.stk = marshalled query contents ∧ run.length ≤ absentBudget core query contents := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceFlag, sourceData, sourceLength⟩ :=
    source_absent_runs core pointer destination query contents store register range
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace HeapLoad.storeIso (sourceProgram core pointer destination) source
      (⟨some startLabel, (store, ()), contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved]; exact sourceFlag
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.InputLoad
