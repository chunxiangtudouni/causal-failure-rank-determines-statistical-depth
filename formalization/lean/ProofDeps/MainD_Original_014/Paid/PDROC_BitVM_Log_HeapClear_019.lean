module

public import Paid.PDROC_BitVM_Log_HeapPointer_014
public import Paid.PDROC_BitVM_Kernel_Clear_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.Log.HeapClear

open Turing
open PDROC.BitVM.Native

/-! Only an actual-call/store adapter for the parent's checked clear code.
There is no second clear implementation or induction. Old inactive stacks
are arbitrary; FALSE padding is physically popped rather than treated empty. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Fin 2
abbrev Extra := Unit × Lookup.Store
abbrev SourceStore := Option Bool × Extra
abbrev Store := HeapPointer.Store
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store

def storeIso : SourceStore ≃ Store where
  toFun := fun store => ((store.1, store.2.1), store.2.2)
  invFun := fun store => (store.1.1, (store.1.2, store.2))
  left_inv := by intro store; rfl
  right_inv := by intro store; rfl

def sourceProgram (target : Stack) (label : Label) : TM2.Stmt Alphabet Label SourceStore :=
  if label = 0 then Inline.statement (τ := Extra) (fun _ : Unit => (0 : Label)) 1 (Kernel.Clear.program target ())
  else .halt

def program (target : Stack) := StoreIso.machine storeIso (sourceProgram target)

def sourceState (label : Option Label) (store : SourceStore) (contents : Stack → List Bool) : SourceState :=
  ⟨label, store, contents⟩

theorem agrees (target : Stack) : ∀ label : Unit,
    sourceProgram target ((fun _ : Unit => (0 : Label)) label) =
      Inline.statement (τ := Extra) (fun _ : Unit => (0 : Label)) 1 (Kernel.Clear.program target label) := by
  intro label; cases label; rfl

theorem supports (target : Stack) : TM2.Supports (program target) (Finset.univ : Finset Label) := by
  apply StoreIso.supports storeIso (sourceProgram target) (Finset.univ : Finset Label)
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    · apply Inline.supports_statement (fun _ : Unit => (0 : Label)) 1
        (Finset.univ : Finset Unit) (Finset.univ : Finset Label)
      · intro index _; exact Finset.mem_univ _
      · exact Finset.mem_univ _
      · exact (Kernel.Clear.supports target).2 () (Finset.mem_univ _)
    · simp [sourceProgram, TM2.SupportsStmt]

theorem source_runs (target : Stack) (contents : Stack → List Bool) (store : SourceStore) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (sourceState (some 0) store contents) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram target) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram target) after = none ∧
      after.l = none ∧ after.var = (none, store.2) ∧
      after.stk = Function.update contents target [] ∧ run.length = (contents target).length + 3 := by
  obtain ⟨source, sourceHead, sourceChain, sourceLast, sourceHalt, sourceLength, sourceFrame⟩ :=
    Kernel.Clear.runs target contents store.1
  obtain ⟨returned, after, head, chain, last, label, data, saved, length⟩ :=
    Inline.actual_return_trace (fun _ : Unit => (0 : Label)) 1 (Kernel.Clear.program target)
      (sourceProgram target) (agrees target) source
      (⟨some (), store.1, contents⟩ : Kernel.Clear.State)
      (⟨none, none, Function.update contents target []⟩ : Kernel.Clear.State)
      store.2 sourceHead sourceChain sourceLast sourceHalt
  have afterEq : after = sourceState (some 1) (none, store.2) (Function.update contents target []) := by
    rcases after with ⟨currentLabel, vars, current⟩
    change currentLabel = some 1 at label
    change vars = (none, store.2) at saved
    change current = Function.update contents target [] at data
    subst currentLabel; subst vars; subst current
    rfl
  let final := sourceState none (none, store.2) (Function.update contents target [])
  let run := returned ++ [final]
  have entry : returned.head? = some (sourceState (some 0) store contents) := head
  have actual : run.IsChain (fun a b => TM2.step (sourceProgram target) a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    rw [afterEq]
    rfl
  refine ⟨run, final, ?_, actual, List.getLast?_append_cons returned final [], rfl, rfl, rfl, rfl, ?_⟩
  · change (returned ++ [final]).head? = some (sourceState (some 0) store contents)
    simp only [List.head?_append, entry, Option.some_or]
  · simp only [run, List.length_append, List.length_cons, List.length_nil]
    omega

/-- ONE selected actual clear-and-return path in the heap family's finite
store. All other31 stacks and all lookup flags retain actual caller data. -/
theorem runs (target : Stack) (contents : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some 0, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program target) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program target) after = none ∧
      after.l = none ∧ after.var = ((none, store.1.2), store.2) ∧
      after.stk = Function.update contents target [] ∧
      run.length = (contents target).length + 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := source_runs target contents (storeIso.symm store)
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso (sourceProgram target) source
      (sourceState (some 0) (storeIso.symm store) contents) sourceFinal
      sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, ?_, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, length.trans sourceLength⟩
  · exact head
  · rw [saved, sourceVar]
    rfl

end PDROC.BitVM.Log.HeapClear
