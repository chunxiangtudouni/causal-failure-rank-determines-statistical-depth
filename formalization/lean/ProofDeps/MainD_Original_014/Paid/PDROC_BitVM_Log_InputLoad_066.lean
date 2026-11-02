module

public import Paid.PDROC_BitVM_Log_InputLoad_065

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.InputLoad

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal

def foundBudget (query : ℕ) (field : Fin 13) (destination : Register) (contents : Stack → List Bool) :=
  selectionBudget query contents + (contents (registerSlot destination)).length +
    2 * (contents (BankDrain.bankSlot field)).length + (encodeNatBits query).length + 12

/-- Whole successful physical input load: actual pointer read, bounded real
Bool search, true readonly Cell copy, true query cleanup and true HALT. -/
theorem source_found_runs (core : Bool) (pointer destination : Register) (query : ℕ)
    (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query))
    (range : query < BankMount.fieldCount core) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.1.2.1 = true ∧
      after.stk = committed ⟨query, by have limit := BankMount.fieldCount_le core; omega⟩ destination (marshalled query contents) ∧
      run.length ≤ foundBudget query ⟨query, by have limit := BankMount.fieldCount_le core; omega⟩ destination contents := by
  let field : Fin 13 := ⟨query, by have limit := BankMount.fieldCount_le core; omega⟩
  obtain ⟨left, vars, leftHead, leftChain, leftLast, matched, leftLength⟩ :=
    selected_prefix_runs core pointer destination query contents store register range
  obtain ⟨right, after, rightHead, rightChain, rightLast, halt, done, flag, data, positive, rightLength⟩ :=
    commit_runs core pointer destination field (marshalled query contents) vars (marshalled_ready query contents).1
  let middle : SourceState := ⟨some (copyLabel field 0), (vars, ()), marshalled query contents⟩
  let run := left ++ right.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, leftHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) :=
    TwoStack.join_chain left right middle leftChain rightChain leftLast rightHead
  have notOne : right.length ≠ 1 := by omega
  have last : run.getLast? = some after := by
    simp only [run, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte, rightLast, Option.some_or]
  refine ⟨run, after, head, chain, last, halt, done, flag, data, ?_⟩
  have rightBound : right.length ≤ (contents (registerSlot destination)).length +
      2 * (contents (BankDrain.bankSlot field)).length + (encodeNatBits query).length + 12 := by
    simpa only [marshalled_register, marshalled_bank, (marshalled_ready query contents).2.1] using rightLength
  change run.length ≤ selectionBudget query contents + (contents (registerSlot destination)).length +
    2 * (contents (BankDrain.bankSlot field)).length + (encodeNatBits query).length + 12
  simp only [run, List.length_append, List.length_tail]
  omega

theorem found_runs (core : Bool) (pointer destination : Register) (query : ℕ)
    (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query))
    (range : query < BankMount.fieldCount core) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program core pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core pointer destination) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = true ∧
      after.stk = committed ⟨query, by have limit := BankMount.fieldCount_le core; omega⟩ destination (marshalled query contents) ∧
      run.length ≤ foundBudget query ⟨query, by have limit := BankMount.fieldCount_le core; omega⟩ destination contents := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt, sourceDone, sourceFlag, sourceData, sourceLength⟩ :=
    source_found_runs core pointer destination query contents store register range
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace HeapLoad.storeIso (sourceProgram core pointer destination) source
      (⟨some startLabel, (store, ()), contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved]; exact sourceFlag
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.InputLoad
