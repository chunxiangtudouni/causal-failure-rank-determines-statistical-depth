module

public import Paid.PDROC_BitVM_Log_HeapPrepend_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.Log.HeapPrepend

open Turing
open PDROC.BitVM.Native

/-! The three actual drains used by this record constructor. PhaseFin3 is
only a compile-time finite code choice: address, Cell and final history.
Every returned route is obtained from ONE checked source drain path. -/

abbrev Phase := Fin 3

def phaseEmbedding (phase : Phase) : Drain.Stack ↪ Stack :=
  if phase = 0 then addressEmbedding else if phase = 1 then cellEmbedding else Lookup.heapWorkEmbed

def phaseMode (phase : Phase) : Bool := if phase = 2 then false else true
def sourceSlot (phase : Phase) : Stack := if phase = 0 then 26 else if phase = 1 then 28 else 25
def targetSlot (phase : Phase) : Stack := if phase = 2 then 21 else 25
def sourceIndex (phase : Phase) : Drain.Stack := if phase = 2 then 2 else 6
def targetIndex (phase : Phase) : Drain.Stack := if phase = 2 then 0 else 5

def phaseSource (phase : Phase) := Lift.machine (phaseEmbedding phase) (Drain.program (phaseMode phase))
def phaseLabel (phase : Phase) : Drain.Label → Label :=
  if phase = 0 then addressLabel else if phase = 1 then cellLabel else historyLabel
def phaseReturn (stored : Bool) (phase : Phase) : Label :=
  if phase = 0 then (if stored then cellLabel 0 else historyLabel 0)
  else if phase = 1 then historyLabel 0 else doneLabel

theorem phase_agrees (stored : Bool) (phase : Phase) : ∀ label,
    sourceProgram stored (phaseLabel phase label) =
      Inline.statement (τ := Extra) (phaseLabel phase) (phaseReturn stored phase) (phaseSource phase label) := by
  intro label
  fin_cases phase <;> rfl

theorem phase_projection (phase : Phase) (contents : Stack → List Bool) (store : Query.Store) :
    Lift.cfg (phaseEmbedding phase) (⟨some 0, store, contents⟩ : DrainState) =
      Drain.state (phaseMode phase) (some 0) store (contents (sourceSlot phase)) (contents (targetSlot phase))
        (fun index => contents (phaseEmbedding phase index)) := by
  fin_cases phase
  · exact address_projection contents store
  · exact cell_projection contents store
  · exact history_projection contents store

theorem phase_slots_distinct (phase : Phase) : sourceSlot phase ≠ targetSlot phase := by
  fin_cases phase <;> decide

/-- An actual finite-stack source drain, with precise source/target commit
and arbitrary old contents on every other slot. No inactive-empty premise. -/
theorem phase_source_runs (phase : Phase) (contents : Stack → List Bool) (store : Query.Store) :
    ∃ (run : List DrainState) (after : DrainState),
      run.head? = some (⟨some 0, store, contents⟩ : DrainState) ∧
      run.IsChain (fun a b => TM2.step (phaseSource phase) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (phaseSource phase) after = none ∧
      after.l = none ∧ after.var = (none, store.2) ∧
      after.stk = Function.update (Function.update contents (sourceSlot phase) []) (targetSlot phase)
        ((contents (sourceSlot phase)).reverse ++ contents (targetSlot phase)) ∧
      run.length = (contents (sourceSlot phase)).length + 3 := by
  let other : Drain.Stack → List Bool := fun index => contents (phaseEmbedding phase index)
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    Drain.drain_runs (phaseMode phase) (contents (sourceSlot phase)) (contents (targetSlot phase)) other store
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq : first = Drain.state (phaseMode phase) (some 0) store
        (contents (sourceSlot phase)) (contents (targetSlot phase)) other := Option.some.inj sourceHead
    subst first
    let before : DrainState := ⟨some 0, store, contents⟩
    obtain ⟨posts, final, length, chain, last, projected, frame⟩ :=
      Lift.path (phaseEmbedding phase) (Drain.program (phaseMode phase)) before
        (Drain.state (phaseMode phase) (some 0) store (contents (sourceSlot phase)) (contents (targetSlot phase)) other)
        sourceFinal rest (phase_projection phase contents store) sourceChain sourceLast
    have halt : TM2.step (phaseSource phase) final = none := by
      apply Lift.halt_project
      rw [projected]
      exact sourceHalt
    have done : final.l = none := (congrArg (fun current : Drain.State => current.l) projected).trans sourceDone
    have saved : final.var = (none, store.2) := (congrArg (fun current : Drain.State => current.var) projected).trans sourceVar
    have localData (index : Drain.Stack) : final.stk (phaseEmbedding phase index) =
        Drain.slots (phaseMode phase) [] ((contents (sourceSlot phase)).reverse ++ contents (targetSlot phase)) other index :=
      (congrArg (fun current : Drain.State => current.stk index) projected).trans (congrFun sourceData index)
    have data : final.stk = Function.update (Function.update contents (sourceSlot phase) []) (targetSlot phase)
        ((contents (sourceSlot phase)).reverse ++ contents (targetSlot phase)) := by
      funext index
      by_cases target : index = targetSlot phase
      · subst index
        rw [Function.update_self]
        have actual := localData (targetIndex phase)
        fin_cases phase <;> simpa [phaseEmbedding, targetIndex, phaseMode, sourceSlot, targetSlot,
          addressEmbedding, cellEmbedding, Lookup.heapWorkEmbed, Drain.slots, Drain.source, Drain.target] using actual
      · rw [Function.update_of_ne target]
        by_cases sourceSlotEq : index = sourceSlot phase
        · subst index
          rw [Function.update_self]
          have actual := localData (sourceIndex phase)
          fin_cases phase <;> simpa [phaseEmbedding, sourceIndex, phaseMode, sourceSlot, targetSlot,
            addressEmbedding, cellEmbedding, Lookup.heapWorkEmbed, Drain.slots, Drain.source, Drain.target] using actual
        · rw [Function.update_of_ne sourceSlotEq]
          by_cases inside : ∃ localIndex, phaseEmbedding phase localIndex = index
          · obtain ⟨localIndex, equal⟩ := inside
            subst index
            have actual := localData localIndex
            fin_cases phase <;> fin_cases localIndex <;>
              simp_all [phaseEmbedding, phaseMode, sourceSlot, targetSlot, addressEmbedding, cellEmbedding,
                Lookup.heapWorkEmbed, Drain.slots, Drain.source, Drain.target, other]
          · exact frame index (by
              intro localIndex equal
              exact inside ⟨localIndex, equal.symm⟩)
    refine ⟨before :: posts, final, rfl, chain, last, halt, done, saved, data, ?_⟩
    simp only [List.length_cons] at sourceLength ⊢
    omega

/-- The selected drain returns into the same real record-constructor code.
The last local halt becomes an actual goto to the next finite phase. -/
theorem phase_return_runs (stored : Bool) (phase : Phase) (contents : Stack → List Bool) (store : SourceStore) :
    ∃ run : List SourceState,
      run.head? = some (sourceState (some (phaseLabel phase 0)) store contents) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram stored) a = some b) ∧
      run.getLast? = some (sourceState (some (phaseReturn stored phase)) ((none, store.1.2), store.2)
        (Function.update (Function.update contents (sourceSlot phase) []) (targetSlot phase)
          ((contents (sourceSlot phase)).reverse ++ contents (targetSlot phase)))) ∧
      run.length = (contents (sourceSlot phase)).length + 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := phase_source_runs phase contents store.1
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace (phaseLabel phase) (phaseReturn stored phase) (phaseSource phase)
      (sourceProgram stored) (phase_agrees stored phase) source
      (⟨some 0, store.1, contents⟩ : DrainState) sourceFinal store.2
      sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = ((none, store.1.2), store.2) := by rw [saved, sourceVar]
  have finalData : after.stk = Function.update (Function.update contents (sourceSlot phase) []) (targetSlot phase)
      ((contents (sourceSlot phase)).reverse ++ contents (targetSlot phase)) := data.trans sourceData
  have afterEq : after = sourceState (some (phaseReturn stored phase)) ((none, store.1.2), store.2)
      (Function.update (Function.update contents (sourceSlot phase) []) (targetSlot phase)
        ((contents (sourceSlot phase)).reverse ++ contents (targetSlot phase))) := by
    rcases after with ⟨label, vars, current⟩
    change label = some (phaseReturn stored phase) at returned
    change vars = ((none, store.1.2), store.2) at finalVar
    change current = _ at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, ?_, chain, ?_, length.trans sourceLength⟩
  · exact head
  · simpa only [afterEq] using last

end PDROC.BitVM.Log.HeapPrepend
