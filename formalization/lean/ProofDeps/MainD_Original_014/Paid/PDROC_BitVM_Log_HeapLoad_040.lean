module

public import Paid.PDROC_BitVM_Log_HeapLoad_039

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

@[expose] public section

namespace PDROC.BitVM.Log.HeapLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

def foundBudget (events : List HeapEvent) (query : ℕ) (destination : Register)
    (value : Cell) (contents : Stack → List Bool) :=
  queryBudget events query contents + (contents (registerSlot destination)).length +
    (encodeNatBits query).length + 3 * (encodeCellBits value).length + 16

theorem looked_fields (events : List HeapEvent) (query : ℕ) (contents : Stack → List Bool) :
    looked events query contents 24 = [] ∧ looked events query contents 26 = encodeNatBits query ∧
      looked events query contents 28 = Lookup.valueBytes (lookup events query) := by
  simp [looked, marshalled, preCleared]

theorem looked_register (events : List HeapEvent) (query : ℕ) (reg : Register) (contents : Stack → List Bool) :
    looked events query contents (registerSlot reg) = contents (registerSlot reg) := by
  cases reg <;> simp [looked, marshalled, preCleared, registerSlot,
    PaperProofs.Structure.LaminarTree.IndexedRAM.Register.word]

/-- The genuine lookup produces the Cell bytes used by the commit. Query
and destination may alias: the source pointer has already been read before
the destination is actually overwritten. ONE selected joined path. -/
theorem source_found_runs (pointer destination : Register) (events : List HeapEvent) (query : ℕ)
    (value : Cell) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query))
    (history : contents 21 = encodeHistory events) (found : lookup events query = some value) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram pointer destination) after = none ∧
      after.l = none ∧ Query.equality after.var.1.2.1 = true ∧
      after.stk = committed destination (looked events query contents) ∧
      run.length ≤ foundBudget events query destination value contents := by
  obtain ⟨left, vars, leftHead, leftChain, leftLast, saved, flag, leftLength⟩ :=
    queried_runs pointer destination events query contents store register history
  have actualFound : (Query.equality vars.2.1 && Query.recordTag vars.2.1) = true := by
    simpa only [found, Option.isSome_some] using flag
  obtain ⟨right, after, rightHead, rightChain, rightLast, halt, done, afterVar, data, rightPositive, rightLength⟩ :=
    commit_runs pointer destination (looked events query contents) vars (looked_fields events query contents).1 actualFound
  let middle : SourceState := ⟨some valueBranch, (vars, ()), looked events query contents⟩
  let run := left ++ right.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, leftHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) :=
    TwoStack.join_chain left right middle leftChain rightChain leftLast rightHead
  have notOne : right.length ≠ 1 := by omega
  have last : run.getLast? = some after := by
    simp only [run, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
      rightLast, Option.some_or]
  refine ⟨run, after, head, chain, last, halt, done, ?_, data, ?_⟩
  · rw [afterVar]; rfl
  · have commitBound : right.length ≤ (contents (registerSlot destination)).length +
        (encodeNatBits query).length + 3 * (encodeCellBits value).length + 16 := by
      simpa only [commitBudget, looked_register, (looked_fields events query contents).2.1,
        (looked_fields events query contents).2.2, found, Lookup.valueBytes] using rightLength
    simp only [run, List.length_append, List.length_tail, foundBudget]
    omega

theorem found_runs (pointer destination : Register) (events : List HeapEvent) (query : ℕ)
    (value : Cell) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query))
    (history : contents 21 = encodeHistory events) (found : lookup events query = some value) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer destination) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = true ∧
      after.stk = committed destination (looked events query contents) ∧
      run.length ≤ foundBudget events query destination value contents := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceFlag, sourceData, sourceLength⟩ :=
    source_found_runs pointer destination events query value contents store register history found
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso (sourceProgram pointer destination) source
      (⟨some startLabel, (store, ()), contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved]; exact sourceFlag
  · rw [length]; exact sourceLength

theorem missing_runs (pointer destination : Register) (events : List HeapEvent) (query : ℕ)
    (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query))
    (history : contents 21 = encodeHistory events) (missing : lookup events query = none) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer destination) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = false ∧ after.stk = looked events query contents ∧
      run.length ≤ queryBudget events query contents + 2 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceFlag, sourceData, sourceLength⟩ :=
    source_missing_runs pointer destination events query contents store register history missing
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso (sourceProgram pointer destination) source
      (⟨some startLabel, (store, ()), contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved]; exact sourceFlag
  · rw [length]; exact sourceLength

theorem rational_runs (pointer destination : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer destination) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = false ∧ after.stk = preCleared 6 contents ∧
      run.length ≤ clearBudget contents + 5 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := source_rational_runs pointer destination value contents store register
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso (sourceProgram pointer destination) source
      (⟨some startLabel, (store, ()), contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved, sourceVar]; rfl
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.HeapLoad
