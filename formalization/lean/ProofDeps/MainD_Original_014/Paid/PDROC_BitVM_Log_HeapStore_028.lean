module

public import Paid.PDROC_BitVM_Log_HeapStore_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.Log.HeapStore

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Real workspace producers. Empty24/25/26 facts are proved from three
actual clears; arbitrary old FALSE padding and all old words are charged. -/

def cleared24 (contents : Stack → List Bool) := Function.update contents 24 []
def cleared25 (contents : Stack → List Bool) := Function.update (cleared24 contents) 25 []
def cleaned (contents : Stack → List Bool) := Function.update (cleared25 contents) 26 []
def clearBudget (contents : Stack → List Bool) := (contents 24).length + (contents 25).length + (contents 26).length + 9
def marshalled (value : ℕ) (contents : Stack → List Bool) :=
  Function.update (cleaned contents) 26 (encodeNatBits value ++ (cleaned contents) 26)

theorem cleaned_work (contents : Stack → List Bool) :
    cleaned contents 24 = [] ∧ cleaned contents 25 = [] ∧ cleaned contents 26 = [] := by
  simp [cleaned, cleared25, cleared24]

theorem cleaned_register (pointer : Register) (contents : Stack → List Bool) :
    cleaned contents (registerSlot pointer) = contents (registerSlot pointer) := by
  cases pointer <;> simp [cleaned, cleared25, cleared24, registerSlot,
    PaperProofs.Structure.LaminarTree.IndexedRAM.Register.word]

theorem cleaned_outside (contents : Stack → List Bool) (index : Stack)
    (not24 : index ≠ 24) (not25 : index ≠ 25) (not26 : index ≠ 26) :
    cleaned contents index = contents index := by
  simp only [cleaned, cleared25, cleared24, Function.update_of_ne not24,
    Function.update_of_ne not25, Function.update_of_ne not26]

/-- Three actual clears joined at their real return boundaries, not three
host resets. No unrelated stack has an entry-empty qualification. -/
theorem clear_prefix_runs (pointer valueSource : Register) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) ∧
      run.getLast? = some (⟨some (pointerLabel 0), (cleared store, ()), cleaned contents⟩ : SourceState) ∧
      run.length ≤ clearBudget contents := by
  obtain ⟨firstTrace, firstHead, firstChain, firstLast, firstLength⟩ := clear_return pointer valueSource 0 contents store
  obtain ⟨secondTrace, secondHead, secondChain, secondLast, secondLength⟩ :=
    clear_return pointer valueSource 1 (cleared24 contents) (cleared store)
  obtain ⟨thirdTrace, thirdHead, thirdChain, thirdLast, thirdLength⟩ :=
    clear_return pointer valueSource 2 (cleared25 contents) (cleared store)
  let middleFirst : SourceState := ⟨some (clearLabel 1 0), (cleared store, ()), cleared24 contents⟩
  let joinedFirst := firstTrace ++ secondTrace.tail
  have joinedFirstHead : joinedFirst.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [joinedFirst, List.head?_append, firstHead, Option.some_or]
    rfl
  have joinedFirstChain : joinedFirst.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) :=
    TwoStack.join_chain firstTrace secondTrace middleFirst firstChain secondChain firstLast secondHead
  have secondNotOne : secondTrace.length ≠ 1 := by omega
  have joinedFirstLast : joinedFirst.getLast? = some (⟨some (clearLabel 2 0),
      (cleared store, ()), cleared25 contents⟩ : SourceState) := by
    simp only [joinedFirst, List.getLast?_append, List.getLast?_tail, secondNotOne, ↓reduceIte,
      secondLast, Option.some_or]
    rfl
  let middleSecond : SourceState := ⟨some (clearLabel 2 0), (cleared store, ()), cleared25 contents⟩
  let joined := joinedFirst ++ thirdTrace.tail
  have joinedHead : joined.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [joined, List.head?_append, joinedFirstHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) :=
    TwoStack.join_chain joinedFirst thirdTrace middleSecond joinedFirstChain thirdChain joinedFirstLast thirdHead
  have thirdNotOne : thirdTrace.length ≠ 1 := by omega
  have joinedLast : joined.getLast? = some (⟨some (pointerLabel 0),
      (cleared store, ()), cleaned contents⟩ : SourceState) := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, thirdNotOne, ↓reduceIte,
      thirdLast, Option.some_or]
    rfl
  refine ⟨joined, joinedHead, joinedChain, joinedLast, ?_⟩
  have firstExact : firstTrace.length = (contents 24).length + 3 := firstLength
  have secondExact : secondTrace.length = (contents 25).length + 3 := by
    simpa [cleared24, workSlot, HeapRelease.workSlot] using secondLength
  have thirdExact : thirdTrace.length = (contents 26).length + 3 := by
    simpa [cleared25, cleared24, workSlot, HeapRelease.workSlot] using thirdLength
  simp only [joined, joinedFirst, List.length_append, List.length_tail, clearBudget]
  omega

/-- Actual workspace clear followed by actual Nat pointer read. No caller
supplies an encoded address, an empty work stack or a successful run oracle. -/
theorem natural_ready (pointer valueSource : Register) (value : ℕ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value)) :
    ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) ∧
      run.getLast? = some (⟨some branchLabel, (pointerResult (cleared store), ()), marshalled value contents⟩ : SourceState) ∧
      run.length ≤ clearBudget contents + (2 * (encodeNatBits value).length + 7) := by
  obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ := clear_prefix_runs pointer valueSource contents store
  have sourceRegister : cleaned contents (registerSlot pointer) = encodeCellBits (.natural value) :=
    (cleaned_register pointer contents).trans register
  obtain ⟨right, rightHead, rightChain, rightLast, rightLength⟩ :=
    natural_pointer_return pointer valueSource value (cleaned contents) (cleared store) sourceRegister (cleaned_work contents).1
  let middle : SourceState := ⟨some (pointerLabel 0), (cleared store, ()), cleaned contents⟩
  let joined := left ++ right.tail
  have joinedHead : joined.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [joined, List.head?_append, leftHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) :=
    TwoStack.join_chain left right middle leftChain rightChain leftLast rightHead
  have notOne : right.length ≠ 1 := by omega
  have joinedLast : joined.getLast? = some (⟨some branchLabel,
      (pointerResult (cleared store), ()), marshalled value contents⟩ : SourceState) := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
      rightLast, Option.some_or]
    rfl
  refine ⟨joined, joinedHead, joinedChain, joinedLast, ?_⟩
  simp only [joined, List.length_append, List.length_tail]
  omega

/-- The same genuine clear prefix precedes actual type failure for Rat.
Every register, heap21, readonly/output and all other work data carry. -/
theorem rational_ready (pointer valueSource : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) ∧
      run.getLast? = some (⟨some branchLabel,
        (HeapPointer.setTyped (HeapPointer.saveTag (cleared store) (some true)) false, ()), cleaned contents⟩ : SourceState) ∧
      run.length ≤ clearBudget contents + 3 := by
  obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ := clear_prefix_runs pointer valueSource contents store
  have sourceRegister : cleaned contents (registerSlot pointer) = encodeCellBits (.rational value) :=
    (cleaned_register pointer contents).trans register
  obtain ⟨right, rightHead, rightChain, rightLast, rightLength⟩ :=
    rational_pointer_return pointer valueSource value (cleaned contents) (cleared store) sourceRegister
  let middle : SourceState := ⟨some (pointerLabel 0), (cleared store, ()), cleaned contents⟩
  let joined := left ++ right.tail
  have joinedHead : joined.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [joined, List.head?_append, leftHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) :=
    TwoStack.join_chain left right middle leftChain rightChain leftLast rightHead
  have notOne : right.length ≠ 1 := by omega
  have joinedLast : joined.getLast? = some (⟨some branchLabel,
      (HeapPointer.setTyped (HeapPointer.saveTag (cleared store) (some true)) false, ()), cleaned contents⟩ : SourceState) := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
      rightLast, Option.some_or]
  refine ⟨joined, joinedHead, joinedChain, joinedLast, ?_⟩
  simp only [joined, List.length_append, List.length_tail]
  omega

end PDROC.BitVM.Log.HeapStore
