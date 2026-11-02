module

public import Paid.PDROC_BitVM_Log_HeapLoad_034

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2300000

@[expose] public section

namespace PDROC.BitVM.Log.HeapLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Fixed six-stage actual clear prefix. The Nat index in these proofs is
bounded by6 and indexes the already finite code labels; it is NOT in sigma,
transition data, a runtime fuel, an extra input or a workspace oracle. -/

def preCleared (count : ℕ) (contents : Stack → List Bool) : Stack → List Bool :=
  fun index => if 24 ≤ index.val ∧ index.val < 24 + count then [] else contents index
def clearEntry (count : ℕ) : Label := if inside : count < 6 then clearLabel ⟨count, inside⟩ 0 else pointerLabel 0
def clearFlags (count : ℕ) (store : Store) := if count = 0 then store else cleared store
def workCap (contents : Stack → List Bool) := (contents 24).length + (contents 25).length +
  (contents 26).length + (contents 27).length + (contents 28).length + (contents 29).length
def clearBudget (contents : Stack → List Bool) := 6 * (workCap contents + 3) + 1

theorem preCleared_zero (contents : Stack → List Bool) : preCleared 0 contents = contents := by
  funext index
  simp only [preCleared, Nat.add_zero]
  have absent : ¬(24 ≤ index.val ∧ index.val < 24) := by omega
  simp only [absent, ↓reduceIte]

theorem preCleared_current (count : ℕ) (inside : count < 6) (contents : Stack → List Bool) :
    preCleared count contents (workSlot ⟨count, inside⟩) = contents (workSlot ⟨count, inside⟩) := by
  simp [preCleared, workSlot]

theorem preCleared_step (count : ℕ) (inside : count < 6) (contents : Stack → List Bool) :
    Function.update (preCleared count contents) (workSlot ⟨count, inside⟩) [] = preCleared (count + 1) contents := by
  funext index
  by_cases here : index = workSlot ⟨count, inside⟩
  · subst index
    rw [Function.update_self]
    simp [preCleared, workSlot]
  · rw [Function.update_of_ne here]
    have different : index.val ≠ 24 + count := by
      intro same
      exact here (Fin.ext same)
    have predicates : (24 ≤ index.val ∧ index.val < 24 + count) ↔
        (24 ≤ index.val ∧ index.val < 24 + (count + 1)) := by omega
    simp only [preCleared, predicates]

theorem workCap_bound (phase : Fin 6) (contents : Stack → List Bool) :
    (contents (workSlot phase)).length ≤ workCap contents := by
  fin_cases phase <;> norm_num [workSlot, workCap] <;> omega

theorem clearFlags_step (count : ℕ) (store : Store) : cleared (clearFlags count store) = clearFlags (count + 1) store := by
  by_cases zero : count = 0 <;> simp [clearFlags, zero, cleared]

/-- The empty boundary path is only the literal zero-stage prefix. Every one
of the six actual clear blocks is then selected and joined with its real call. -/
theorem clear_prefix_runs (pointer destination : Register) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (pointerLabel 0), (cleared store, ()), preCleared 6 contents⟩ : SourceState) ∧
      run.length ≤ clearBudget contents := by
  have build : ∀ count : ℕ, count ≤ 6 → ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (clearEntry count), (clearFlags count store, ()), preCleared count contents⟩ : SourceState) ∧
      run.length ≤ count * (workCap contents + 3) + 1 := by
    intro count
    induction count with
    | zero =>
      intro _
      let first : SourceState := ⟨some startLabel, (store, ()), contents⟩
      refine ⟨[first], rfl, List.isChain_singleton _, ?_, by simp⟩
      simp only [List.getLast?_singleton, clearEntry, clearFlags, preCleared_zero]
      rfl
    | succ count ih =>
      intro bound
      have inside : count < 6 := by omega
      obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ := ih (by omega)
      obtain ⟨right, rightHead, rightChain, rightLast, rightLength⟩ :=
        clear_return pointer destination ⟨count, inside⟩ (preCleared count contents) (clearFlags count store)
      let middle : SourceState := ⟨some (clearEntry count), (clearFlags count store, ()), preCleared count contents⟩
      have rightHeadExact : right.head? = some middle := by
        simpa only [middle, clearEntry, inside, ↓reduceDIte] using rightHead
      let joined := left ++ right.tail
      have head : joined.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
        simp only [joined, List.head?_append, leftHead, Option.some_or]
      have chain : joined.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) :=
        TwoStack.join_chain left right middle leftChain rightChain leftLast rightHeadExact
      have notOne : right.length ≠ 1 := by omega
      have rightLastExact : right.getLast? = some (⟨some (clearEntry (count + 1)),
          (clearFlags (count + 1) store, ()), preCleared (count + 1) contents⟩ : SourceState) := by
        rw [clearFlags_step, preCleared_step] at rightLast
        exact rightLast
      have last : joined.getLast? = some (⟨some (clearEntry (count + 1)),
          (clearFlags (count + 1) store, ()), preCleared (count + 1) contents⟩ : SourceState) := by
        simp only [joined, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
          rightLastExact, Option.some_or]
      refine ⟨joined, head, chain, last, ?_⟩
      have stageLength : right.length ≤ workCap contents + 3 := by
        rw [rightLength, preCleared_current]
        exact Nat.add_le_add_right (workCap_bound ⟨count, inside⟩ contents) 3
      simp only [joined, List.length_append, List.length_tail]
      have tailBound : right.length - 1 ≤ workCap contents + 3 :=
        (Nat.sub_le _ _).trans stageLength
      calc
        left.length + (right.length - 1) ≤ (count * (workCap contents + 3) + 1) + (workCap contents + 3) :=
          Nat.add_le_add leftLength tailBound
        _ = (count + 1) * (workCap contents + 3) + 1 := by ring
  obtain ⟨run, head, chain, last, length⟩ := build 6 (by omega)
  refine ⟨run, head, chain, ?_, length⟩
  simpa [clearEntry, clearFlags] using last

theorem preCleared_work (contents : Stack → List Bool) (phase : Fin 6) :
    preCleared 6 contents (workSlot phase) = [] := by
  fin_cases phase <;> simp [preCleared, workSlot]

theorem preCleared_register (contents : Stack → List Bool) (reg : Register) :
    preCleared 6 contents (Kernel.RegisterGlobal.registerSlot reg) = contents (Kernel.RegisterGlobal.registerSlot reg) := by
  have bound := Kernel.RegisterGlobal.registerSlot_bounds reg
  have outside : ¬24 ≤ (Kernel.RegisterGlobal.registerSlot reg).val := by omega
  simp [preCleared, outside]

theorem preCleared_outside (contents : Stack → List Bool) (index : Stack)
    (outside : index.val < 24 ∨ 30 ≤ index.val) : preCleared 6 contents index = contents index := by
  have absent : ¬(24 ≤ index.val ∧ index.val < 24 + 6) := by omega
  simp only [preCleared, absent, ↓reduceIte]

end PDROC.BitVM.Log.HeapLoad
