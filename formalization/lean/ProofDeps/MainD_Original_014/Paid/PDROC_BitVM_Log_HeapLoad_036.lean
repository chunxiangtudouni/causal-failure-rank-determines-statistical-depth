module

public import Paid.PDROC_BitVM_Log_HeapLoad_035

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.Log.HeapLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Actual six-buffer preparation and same-path lookup return. No encoded
query, caller-empty workspace or successful lookup is an extra input. -/

def marshalled (value : ℕ) (contents : Stack → List Bool) :=
  Function.update (preCleared 6 contents) 26 (encodeNatBits value ++ preCleared 6 contents 26)

/-- Actual workspace clear followed by actual Nat pointer read. No caller
supplies an encoded address, an empty work stack or a successful run oracle. -/
theorem natural_ready (pointer destination : Register) (value : ℕ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value)) :
    ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some (⟨some typeBranch, (pointerResult (cleared store), ()), marshalled value contents⟩ : SourceState) ∧
      run.length ≤ clearBudget contents + (2 * (encodeNatBits value).length + 7) := by
  obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ := clear_prefix_runs pointer destination contents store
  have sourceRegister : (preCleared 6 contents) (registerSlot pointer) = encodeCellBits (.natural value) :=
    (preCleared_register contents pointer).trans register
  obtain ⟨right, rightHead, rightChain, rightLast, rightLength⟩ :=
    natural_pointer_return pointer destination value ((preCleared 6 contents)) (cleared store) sourceRegister (preCleared_work contents 0)
  let middle : SourceState := ⟨some (pointerLabel 0), (cleared store, ()), (preCleared 6 contents)⟩
  let joined := left ++ right.tail
  have joinedHead : joined.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [joined, List.head?_append, leftHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) :=
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
theorem rational_ready (pointer destination : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some (⟨some typeBranch,
        (HeapPointer.setTyped (HeapPointer.saveTag (cleared store) (some true)) false, ()), (preCleared 6 contents)⟩ : SourceState) ∧
      run.length ≤ clearBudget contents + 3 := by
  obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ := clear_prefix_runs pointer destination contents store
  have sourceRegister : (preCleared 6 contents) (registerSlot pointer) = encodeCellBits (.rational value) :=
    (preCleared_register contents pointer).trans register
  obtain ⟨right, rightHead, rightChain, rightLast, rightLength⟩ :=
    rational_pointer_return pointer destination value ((preCleared 6 contents)) (cleared store) sourceRegister
  let middle : SourceState := ⟨some (pointerLabel 0), (cleared store, ()), (preCleared 6 contents)⟩
  let joined := left ++ right.tail
  have joinedHead : joined.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [joined, List.head?_append, leftHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) :=
    TwoStack.join_chain left right middle leftChain rightChain leftLast rightHead
  have notOne : right.length ≠ 1 := by omega
  have joinedLast : joined.getLast? = some (⟨some typeBranch,
      (HeapPointer.setTyped (HeapPointer.saveTag (cleared store) (some true)) false, ()), (preCleared 6 contents)⟩ : SourceState) := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
      rightLast, Option.some_or]
  refine ⟨joined, joinedHead, joinedChain, joinedLast, ?_⟩
  simp only [joined, List.length_append, List.length_tail]
  omega

/-- The selected genuine lookup path is embedded once in the load caller.
The flag is actual latest-record status, including a matched tombstone. -/
theorem lookup_return (pointer destination : Register) (events : List HeapEvent) (query : ℕ)
    (contents : Stack → List Bool) (store : Store)
    (history : contents 21 = encodeHistory events) (work24 : contents 24 = [])
    (work25 : contents 25 = []) (address : contents 26 = encodeNatBits query)
    (work27 : contents 27 = []) (work28 : contents 28 = []) (work29 : contents 29 = []) :
    ∃ (run : List SourceState) (vars : Store) (data : Stack → List Bool),
      run.head? = some (⟨some (lookupLabel HeapLookup.startLabel), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some (⟨some valueBranch, (vars, ()), data⟩ : SourceState) ∧
      vars.1 = store.1 ∧
      (Query.equality vars.2.1 && Query.recordTag vars.2.1) = (lookup events query).isSome ∧
      Lift.slots Lookup.heapWorkEmbed data = Lookup.slots (encodeHistory events) [] (encodeNatBits query)
        (Lookup.valueBytes (lookup events query)) ∧
      (∀ index : Stack, (∀ localIndex, Lookup.heapWorkEmbed localIndex ≠ index) → data index = contents index) ∧
      run.length ≤ 100 * (events.length + 1) * ((encodeHistory events).length + 1) + 1 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceSaved, sourceFlag, sourceData, sourceFrame, sourceLength⟩ :=
    HeapLookup.runs events query contents store history work24 work25 address work27 work28 work29
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace lookupLabel valueBranch HeapLookup.program
      (sourceProgram pointer destination) (lookup_agrees pointer destination) source
      (⟨some HeapLookup.startLabel, store, contents⟩ : HeapLookup.State) sourceFinal ()
      sourceHead sourceChain sourceLast sourceHalt
  have afterEq : after = (⟨some valueBranch, (sourceFinal.var, ()), sourceFinal.stk⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some valueBranch at returned
    change vars = (sourceFinal.var, ()) at saved
    change current = sourceFinal.stk at data
    subst label; subst vars; subst current
    rfl
  refine ⟨run, sourceFinal.var, sourceFinal.stk, head, chain, ?_, sourceSaved,
    sourceFlag, sourceData, sourceFrame, ?_⟩
  · simpa only [afterEq] using last
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.HeapLoad
