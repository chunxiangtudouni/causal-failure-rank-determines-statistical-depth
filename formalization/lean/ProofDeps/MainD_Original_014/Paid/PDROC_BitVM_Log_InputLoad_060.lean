module

public import Paid.PDROC_BitVM_Log_InputLoad_059

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

namespace PDROC.BitVM.Log.InputLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal

/-! Genuine old-work clears and true Nat/Rat pointer read into THIS input
opcode's actual program. No caller encoded address or successful run oracle. -/

def cleared (store : Store) := HeapLoad.cleared store
def pointerResult (store : Store) := HeapLoad.pointerResult store

theorem clear_return (core : Bool) (pointer destination : Register) (phase : Fin 6) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (clearLabel phase 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some (nextClear phase), (cleared store, ()),
        Function.update contents (workSlot phase) []⟩ : SourceState) ∧
      run.length = (contents (workSlot phase)).length + 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapClear.runs (workSlot phase) contents store
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace (clearLabel phase) (nextClear phase) (HeapClear.program (workSlot phase))
      (sourceProgram core pointer destination) (clear_agrees core pointer destination phase) source
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

theorem natural_pointer_return (core : Bool) (pointer destination : Register) (value : ℕ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value))
    (scratch : contents 24 = []) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (pointerLabel 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some typeBranch, (pointerResult store, ()),
        Function.update contents 26 (encodeNatBits value ++ contents 26)⟩ : SourceState) ∧
      run.length = 2 * (encodeNatBits value).length + 7 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapPointer.natural_runs pointer value contents store register scratch
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace pointerLabel typeBranch (HeapPointer.program pointer)
      (sourceProgram core pointer destination) (pointer_agrees core pointer destination) source
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

theorem rational_pointer_return (core : Bool) (pointer destination : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (pointerLabel 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some typeBranch,
        (HeapPointer.setTyped (HeapPointer.saveTag store (some true)) false, ()), contents⟩ : SourceState) ∧
      run.length = 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapPointer.rational_runs pointer value contents store register
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace pointerLabel typeBranch (HeapPointer.program pointer)
      (sourceProgram core pointer destination) (pointer_agrees core pointer destination) source
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

theorem clean_return (core : Bool) (pointer destination : Register) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (cleanLabel 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core pointer destination) a = some b) ∧
      run.getLast? = some (⟨some doneLabel, (cleared store, ()), Function.update contents 26 []⟩ : SourceState) ∧
      run.length = (contents 26).length + 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapClear.runs 26 contents store
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace cleanLabel doneLabel (HeapClear.program 26)
      (sourceProgram core pointer destination) (clean_agrees core pointer destination) source
      (⟨some 0, store, contents⟩ : HeapClear.State) sourceFinal () sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (cleared store, ()) := by rw [saved, sourceVar]; rfl
  have finalData : after.stk = Function.update contents 26 [] := data.trans sourceData
  have afterEq : after = (⟨some doneLabel, (cleared store, ()), Function.update contents 26 []⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some doneLabel at returned
    change vars = (cleared store, ()) at finalVar
    change current = Function.update contents 26 [] at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, length.trans sourceLength⟩
  simpa only [afterEq] using last

end PDROC.BitVM.Log.InputLoad
