module

public import Paid.PDROC_BitVM_Log_HeapLoad_033

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.Log.HeapLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Actual component returns into the ONE release opcode program. Each path
is selected once from an already proved clear/pointer/prepend run, with real
return jumps and preserved caller Unit. No source-function oracle is assumed. -/

def cleared (store : Store) : Store := ((none, store.1.2), store.2)
def pointerResult (store : Store) := HeapPointer.setTyped ((none, ()), store.2) true
def prependResult (store : Store) : Store := (store.1, ((none, store.2.1.2), store.2.2))

theorem clear_return (pointer destination : Register) (phase : Fin 6) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (clearLabel phase 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (nextClear phase), (cleared store, ()),
        Function.update contents (workSlot phase) []⟩ : SourceState) ∧
      run.length = (contents (workSlot phase)).length + 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapClear.runs (workSlot phase) contents store
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace (clearLabel phase) (nextClear phase) (HeapClear.program (workSlot phase))
      (sourceProgram pointer destination) (clear_agrees pointer destination phase) source
      (⟨some 0, store, contents⟩ : HeapClear.State) sourceFinal () sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (cleared store, ()) := by rw [saved, sourceVar]; rfl
  have finalData : after.stk = Function.update contents (workSlot phase) [] := data.trans sourceData
  have afterEq : after = (⟨some (nextClear phase), (cleared store, ()),
      Function.update contents (workSlot phase) []⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some (nextClear phase) at returned
    change vars = (cleared store, ()) at finalVar
    change current = _ at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, length.trans sourceLength⟩
  simpa only [afterEq] using last

theorem natural_pointer_return (pointer destination : Register) (value : ℕ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value))
    (scratch : contents 24 = []) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (pointerLabel 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some (⟨some typeBranch, (pointerResult store, ()),
        Function.update contents 26 (encodeNatBits value ++ contents 26)⟩ : SourceState) ∧
      run.length = 2 * (encodeNatBits value).length + 7 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapPointer.natural_runs pointer value contents store register scratch
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace pointerLabel typeBranch (HeapPointer.program pointer)
      (sourceProgram pointer destination) (pointer_agrees pointer destination) source
      (HeapPointer.state (some 0) store contents) sourceFinal () sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (pointerResult store, ()) := by rw [saved, sourceVar]; rfl
  have finalData : after.stk = Function.update contents 26 (encodeNatBits value ++ contents 26) := data.trans sourceData
  have afterEq : after = (⟨some typeBranch, (pointerResult store, ()),
      Function.update contents 26 (encodeNatBits value ++ contents 26)⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some typeBranch at returned
    change vars = (pointerResult store, ()) at finalVar
    change current = _ at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, length.trans sourceLength⟩
  simpa only [afterEq] using last

theorem rational_pointer_return (pointer destination : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (pointerLabel 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some (⟨some typeBranch,
        (HeapPointer.setTyped (HeapPointer.saveTag store (some true)) false, ()), contents⟩ : SourceState) ∧
      run.length = 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapPointer.rational_runs pointer value contents store register
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace pointerLabel typeBranch (HeapPointer.program pointer)
      (sourceProgram pointer destination) (pointer_agrees pointer destination) source
      (HeapPointer.state (some 0) store contents) sourceFinal () sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (HeapPointer.setTyped (HeapPointer.saveTag store (some true)) false, ()) := by rw [saved, sourceVar]
  have finalData : after.stk = contents := data.trans sourceData
  have afterEq : after = (⟨some typeBranch,
      (HeapPointer.setTyped (HeapPointer.saveTag store (some true)) false, ()), contents⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some typeBranch at returned
    change vars = (HeapPointer.setTyped (HeapPointer.saveTag store (some true)) false, ()) at finalVar
    change current = contents at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, length.trans sourceLength⟩
  simpa only [afterEq] using last

theorem transfer_return (pointer destination : Register) (contents : Stack → List Bool) (store : Store)
    (scratch : contents 24 = []) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (transferLabel 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (postLabel 0 0), (cleared store, ()),
        Function.update contents (registerSlot destination) (contents 28)⟩ : SourceState) ∧
      run.length = (contents (registerSlot destination)).length + 2 * (contents 28).length + 6 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapTransfer.runs true destination contents store scratch
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace transferLabel (postLabel 0 0) (HeapTransfer.program true destination)
      (sourceProgram pointer destination) (transfer_agrees pointer destination) source
      (⟨some 0, store, contents⟩ : HeapTransfer.State) sourceFinal ()
      sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (cleared store, ()) := by rw [saved, sourceVar]; rfl
  have finalData : after.stk = Function.update contents (registerSlot destination) (contents 28) := data.trans sourceData
  have afterEq : after = (⟨some (postLabel 0 0), (cleared store, ()),
      Function.update contents (registerSlot destination) (contents 28)⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some (postLabel 0 0) at returned
    change vars = (cleared store, ()) at finalVar
    change current = _ at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, length.trans sourceLength⟩
  simpa only [afterEq] using last

theorem post_return (pointer destination : Register) (phase : Fin 2) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (postLabel phase 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (nextPost phase), (cleared store, ()),
        Function.update contents (postSlot phase) []⟩ : SourceState) ∧
      run.length = (contents (postSlot phase)).length + 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapClear.runs (postSlot phase) contents store
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace (postLabel phase) (nextPost phase) (HeapClear.program (postSlot phase))
      (sourceProgram pointer destination) (post_agrees pointer destination phase) source
      (⟨some 0, store, contents⟩ : HeapClear.State) sourceFinal () sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (cleared store, ()) := by rw [saved, sourceVar]; rfl
  have finalData : after.stk = Function.update contents (postSlot phase) [] := data.trans sourceData
  have afterEq : after = (⟨some (nextPost phase), (cleared store, ()),
      Function.update contents (postSlot phase) []⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some (nextPost phase) at returned
    change vars = (cleared store, ()) at finalVar
    change current = _ at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, length.trans sourceLength⟩
  simpa only [afterEq] using last

end PDROC.BitVM.Log.HeapLoad
