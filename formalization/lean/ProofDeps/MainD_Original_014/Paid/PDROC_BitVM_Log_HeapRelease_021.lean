module

public import Paid.PDROC_BitVM_Log_HeapRelease_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.Log.HeapRelease

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Actual component returns into the ONE release opcode program. Each path
is selected once from an already proved clear/pointer/prepend run, with real
return jumps and preserved caller Unit. No source-function oracle is assumed. -/

def cleared (store : Store) : Store := ((none, store.1.2), store.2)
def pointerResult (store : Store) := HeapPointer.setTyped ((none, ()), store.2) true
def prependResult (store : Store) : Store := (store.1, ((none, store.2.1.2), store.2.2))

theorem clear_return (pointer : Register) (phase : Fin 3) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (clearLabel phase 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) ∧
      run.getLast? = some (⟨some (nextClear phase), (cleared store, ()),
        Function.update contents (workSlot phase) []⟩ : SourceState) ∧
      run.length = (contents (workSlot phase)).length + 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapClear.runs (workSlot phase) contents store
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace (clearLabel phase) (nextClear phase) (HeapClear.program (workSlot phase))
      (sourceProgram pointer) (clear_agrees pointer phase) source
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

theorem natural_pointer_return (pointer : Register) (value : ℕ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value))
    (scratch : contents 24 = []) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (pointerLabel 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) ∧
      run.getLast? = some (⟨some branchLabel, (pointerResult store, ()),
        Function.update contents 26 (encodeNatBits value ++ contents 26)⟩ : SourceState) ∧
      run.length = 2 * (encodeNatBits value).length + 7 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapPointer.natural_runs pointer value contents store register scratch
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace pointerLabel branchLabel (HeapPointer.program pointer)
      (sourceProgram pointer) (pointer_agrees pointer) source
      (HeapPointer.state (some 0) store contents) sourceFinal () sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (pointerResult store, ()) := by rw [saved, sourceVar]; rfl
  have finalData : after.stk = Function.update contents 26 (encodeNatBits value ++ contents 26) := data.trans sourceData
  have afterEq : after = (⟨some branchLabel, (pointerResult store, ()),
      Function.update contents 26 (encodeNatBits value ++ contents 26)⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some branchLabel at returned
    change vars = (pointerResult store, ()) at finalVar
    change current = _ at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, length.trans sourceLength⟩
  simpa only [afterEq] using last

theorem rational_pointer_return (pointer : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (pointerLabel 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) ∧
      run.getLast? = some (⟨some branchLabel,
        (HeapPointer.setTyped (HeapPointer.saveTag store (some true)) false, ()), contents⟩ : SourceState) ∧
      run.length = 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapPointer.rational_runs pointer value contents store register
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace pointerLabel branchLabel (HeapPointer.program pointer)
      (sourceProgram pointer) (pointer_agrees pointer) source
      (HeapPointer.state (some 0) store contents) sourceFinal () sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (HeapPointer.setTyped (HeapPointer.saveTag store (some true)) false, ()) := by rw [saved, sourceVar]
  have finalData : after.stk = contents := data.trans sourceData
  have afterEq : after = (⟨some branchLabel,
      (HeapPointer.setTyped (HeapPointer.saveTag store (some true)) false, ()), contents⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some branchLabel at returned
    change vars = (HeapPointer.setTyped (HeapPointer.saveTag store (some true)) false, ()) at finalVar
    change current = contents at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, length.trans sourceLength⟩
  simpa only [afterEq] using last

theorem prepend_return (pointer : Register) (contents : Stack → List Bool) (store : Store)
    (archive : contents 25 = []) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (prependLabel HeapPrepend.startLabel), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) ∧
      run.getLast? = some (⟨some doneLabel, (prependResult store, ()), HeapPrepend.recordContents false contents⟩ : SourceState) ∧
      run.length ≤ 20 * ((contents 26).length + 1) := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapPrepend.runs false contents store archive
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace prependLabel doneLabel (HeapPrepend.program false)
      (sourceProgram pointer) (prepend_agrees pointer) source
      (⟨some HeapPrepend.startLabel, store, contents⟩ : HeapPrepend.State) sourceFinal ()
      sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (prependResult store, ()) := by rw [saved, sourceVar]; rfl
  have finalData : after.stk = HeapPrepend.recordContents false contents := data.trans sourceData
  have afterEq : after = (⟨some doneLabel, (prependResult store, ()), HeapPrepend.recordContents false contents⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some doneLabel at returned
    change vars = (prependResult store, ()) at finalVar
    change current = _ at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, ?_⟩
  · simpa only [afterEq] using last
  · rw [length]
    change source.length ≤ 20 * ((contents 26).length + 1) at sourceLength
    exact sourceLength

end PDROC.BitVM.Log.HeapRelease
