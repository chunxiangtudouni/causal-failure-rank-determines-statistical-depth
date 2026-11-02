module

public import Paid.PDROC_BitVM_Log_InputLoad_061

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.InputLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

/-! The six emptiness facts are PRODUCED by six actual clear calls in this
opcode program. Only the already passed pure prefix math is reused from the
heap-load line; its execution theorem is not reused for different code. -/

abbrev preCleared := HeapLoad.preCleared
abbrev clearFlags := HeapLoad.clearFlags
abbrev workCap := HeapLoad.workCap
abbrev clearBudget := HeapLoad.clearBudget
abbrev marshalled := HeapLoad.marshalled

def clearEntry (count : ℕ) : Label := if inside : count < 6 then clearLabel ⟨count, inside⟩ 0 else pointerLabel 0

theorem workSlot_eq (stage : Fin 6) : workSlot stage = HeapLoad.workSlot stage := rfl

theorem clear_prefix_runs (core : Bool) (pointer destination : Register) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (pointerLabel 0), (cleared store, ()), preCleared 6 contents⟩ : SourceState) ∧
      run.length ≤ clearBudget contents := by
  have build : ∀ count : ℕ, count ≤ 6 → ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (clearEntry count), (clearFlags count store, ()), preCleared count contents⟩ : SourceState) ∧
      run.length ≤ count * (workCap contents + 3) + 1 := by
    intro count
    induction count with
    | zero =>
      intro _
      let first : SourceState := ⟨some startLabel, (store, ()), contents⟩
      refine ⟨[first], rfl, List.isChain_singleton _, ?_, by simp⟩
      simp only [List.getLast?_singleton, clearEntry, clearFlags, HeapLoad.preCleared_zero]
      rfl
    | succ count ih =>
      intro bound
      have inside : count < 6 := by omega
      obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ := ih (by omega)
      obtain ⟨right, rightHead, rightChain, rightLast, rightLength⟩ :=
        clear_return core pointer destination ⟨count, inside⟩ (preCleared count contents) (clearFlags count store)
      rw [workSlot_eq] at rightLast rightLength
      simp only [cleared] at rightLast
      let middle : SourceState := ⟨some (clearEntry count), (clearFlags count store, ()), preCleared count contents⟩
      have rightHeadExact : right.head? = some middle := by
        simpa only [middle, clearEntry, inside, ↓reduceDIte] using rightHead
      let joined := left ++ right.tail
      have head : joined.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
        simp only [joined, List.head?_append, leftHead, Option.some_or]
      have chain : joined.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) :=
        TwoStack.join_chain left right middle leftChain rightChain leftLast rightHeadExact
      have notOne : right.length ≠ 1 := by omega
      have rightLastExact : right.getLast? = some (⟨some (clearEntry (count + 1)),
          (clearFlags (count + 1) store, ()), preCleared (count + 1) contents⟩ : SourceState) := by
        rw [HeapLoad.clearFlags_step, HeapLoad.preCleared_step] at rightLast
        exact rightLast
      have last : joined.getLast? = some (⟨some (clearEntry (count + 1)),
          (clearFlags (count + 1) store, ()), preCleared (count + 1) contents⟩ : SourceState) := by
        simp only [joined, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
          rightLastExact, Option.some_or]
      refine ⟨joined, head, chain, last, ?_⟩
      have stageLength : right.length ≤ workCap contents + 3 := by
        rw [rightLength]
        change (HeapLoad.preCleared count contents (HeapLoad.workSlot ⟨count, inside⟩)).length + 3 ≤ HeapLoad.workCap contents + 3
        rw [HeapLoad.preCleared_current]
        exact Nat.add_le_add_right (HeapLoad.workCap_bound ⟨count, inside⟩ contents) 3
      simp only [joined, List.length_append, List.length_tail]
      have tailBound : right.length - 1 ≤ workCap contents + 3 :=
        (Nat.sub_le _ _).trans stageLength
      calc
        left.length + (right.length - 1) ≤ (count * (workCap contents + 3) + 1) + (workCap contents + 3) :=
          Nat.add_le_add leftLength tailBound
        _ = (count + 1) * (workCap contents + 3) + 1 := by ring
  obtain ⟨run, head, chain, last, length⟩ := build 6 (by omega)
  refine ⟨run, head, chain, ?_, length⟩
  simpa [clearEntry, clearFlags, HeapLoad.clearFlags, cleared] using last

/-- Actual workspace clear followed by actual Nat pointer read. No caller
supplies an encoded address, an empty work stack or a successful run oracle. -/
theorem natural_ready (core : Bool) (pointer destination : Register) (value : ℕ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value)) :
    ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some typeBranch, (pointerResult (cleared store), ()), marshalled value contents⟩ : SourceState) ∧
      run.length ≤ clearBudget contents + (2 * (encodeNatBits value).length + 7) := by
  obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ := clear_prefix_runs core pointer destination contents store
  have sourceRegister : (preCleared 6 contents) (registerSlot pointer) = encodeCellBits (.natural value) :=
    (HeapLoad.preCleared_register contents pointer).trans register
  obtain ⟨right, rightHead, rightChain, rightLast, rightLength⟩ :=
    natural_pointer_return core pointer destination value ((preCleared 6 contents)) (cleared store) sourceRegister (HeapLoad.preCleared_work contents 0)
  let middle : SourceState := ⟨some (pointerLabel 0), (cleared store, ()), (preCleared 6 contents)⟩
  let joined := left ++ right.tail
  have joinedHead : joined.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [joined, List.head?_append, leftHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) :=
    TwoStack.join_chain left right middle leftChain rightChain leftLast rightHead
  have notOne : right.length ≠ 1 := by omega
  have joinedLast : joined.getLast? = some (⟨some typeBranch,
      (pointerResult (cleared store), ()), marshalled value contents⟩ : SourceState) := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
      rightLast, Option.some_or]
    rfl
  refine ⟨joined, joinedHead, joinedChain, joinedLast, ?_⟩
  simp only [joined, List.length_append, List.length_tail]
  omega

/-- The same genuine clear prefix precedes actual type failure for Rat.
Every register, heap21, readonly/output and all other work data carry. -/
theorem rational_ready (core : Bool) (pointer destination : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some typeBranch,
        (HeapPointer.setTyped (HeapPointer.saveTag (cleared store) (some true)) false, ()), (preCleared 6 contents)⟩ : SourceState) ∧
      run.length ≤ clearBudget contents + 3 := by
  obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ := clear_prefix_runs core pointer destination contents store
  have sourceRegister : (preCleared 6 contents) (registerSlot pointer) = encodeCellBits (.rational value) :=
    (HeapLoad.preCleared_register contents pointer).trans register
  obtain ⟨right, rightHead, rightChain, rightLast, rightLength⟩ :=
    rational_pointer_return core pointer destination value ((preCleared 6 contents)) (cleared store) sourceRegister
  let middle : SourceState := ⟨some (pointerLabel 0), (cleared store, ()), (preCleared 6 contents)⟩
  let joined := left ++ right.tail
  have joinedHead : joined.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [joined, List.head?_append, leftHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) :=
    TwoStack.join_chain left right middle leftChain rightChain leftLast rightHead
  have notOne : right.length ≠ 1 := by omega
  have joinedLast : joined.getLast? = some (⟨some typeBranch,
      (HeapPointer.setTyped (HeapPointer.saveTag (cleared store) (some true)) false, ()), (preCleared 6 contents)⟩ : SourceState) := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
      rightLast, Option.some_or]
  refine ⟨joined, joinedHead, joinedChain, joinedLast, ?_⟩
  simp only [joined, List.length_append, List.length_tail]
  omega


end PDROC.BitVM.Log.InputLoad
