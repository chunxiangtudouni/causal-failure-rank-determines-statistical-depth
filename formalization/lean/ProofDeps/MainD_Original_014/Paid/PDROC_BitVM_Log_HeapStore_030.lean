module

public import Paid.PDROC_BitVM_Log_HeapStore_029

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2100000

@[expose] public section

namespace PDROC.BitVM.Log.HeapStore

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

/-! The actual invalid-pointer route and the same-source-path store transport.
All payload bytes were produced by the real register copy before prepend. -/

theorem source_rational_runs (pointer valueSource : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram pointer valueSource) after = none ∧
      after.l = none ∧ after.var = (rationalResult store, ()) ∧ after.stk = cleaned contents ∧
      run.length ≤ clearBudget contents + 5 := by
  obtain ⟨readyTrace, readyHead, readyChain, readyLast, readyLength⟩ := rational_ready pointer valueSource value contents store register
  let beforeBranch : SourceState := ⟨some branchLabel, (rationalResult store, ()), cleaned contents⟩
  let invalid : SourceState := ⟨some invalidLabel, (rationalResult store, ()), cleaned contents⟩
  let final : SourceState := ⟨none, (rationalResult store, ()), cleaned contents⟩
  let tailTrace := [beforeBranch, invalid, final]
  have tailHead : tailTrace.head? = some beforeBranch := rfl
  have tailChain : tailTrace.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) := by
    apply List.isChain_cons_cons.mpr
    refine ⟨branch_invalid pointer valueSource (rationalResult store, ()) (cleaned contents) rfl, ?_⟩
    exact List.isChain_cons_cons.mpr ⟨invalid_halt pointer valueSource (rationalResult store, ()) (cleaned contents), List.isChain_singleton _⟩
  let run := readyTrace ++ tailTrace.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, readyHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) :=
    TwoStack.join_chain readyTrace tailTrace beforeBranch readyChain tailChain readyLast tailHead
  have last : run.getLast? = some final := by
    simp only [run, tailTrace, List.tail_cons, List.getLast?_append, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.some_or]
  refine ⟨run, final, head, chain, last, rfl, rfl, rfl, rfl, ?_⟩
  simp only [run, tailTrace, List.tail_cons, List.length_append, List.length_cons, List.length_nil]
  omega

theorem natural_runs (pointer valueSource : Register) (value : ℕ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value)) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program pointer valueSource) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer valueSource) after = none ∧
      after.l = none ∧ after.var = naturalResult store ∧ after.stk = stored value valueSource contents ∧
      run.length ≤ clearBudget contents + (contents 28).length + 50 * ((encodeNatBits value).length + (contents (registerSlot valueSource)).length + 1) := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := source_natural_runs pointer valueSource value contents store register
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso (sourceProgram pointer valueSource) source
      (⟨some startLabel, (store, ()), contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved, sourceVar]; rfl
  · rw [length]; exact sourceLength

theorem rational_runs (pointer valueSource : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program pointer valueSource) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer valueSource) after = none ∧
      after.l = none ∧ after.var = rationalResult store ∧ after.stk = cleaned contents ∧
      run.length ≤ clearBudget contents + 5 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := source_rational_runs pointer valueSource value contents store register
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso (sourceProgram pointer valueSource) source
      (⟨some startLabel, (store, ()), contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved, sourceVar]; rfl
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.HeapStore
