module

public import Paid.PDROC_BitVM_Log_BankField_045

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.Log.BankFieldRoot

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native

/-! Finite store adapter only. The actual field reader's ONE selected path
is embedded in the same108-flag store as parent real clears and heap code.
No Nat/Cell/list is stored in sigma, and no caller data is installed by host. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := BankField.Label ⊕ Unit
abbrev SourceStore := BankField.Store × Kernel.NatMarshal.Store
abbrev Store := HeapPointer.Store
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store

def startLabel : Label := .inl BankField.startLabel
def doneLabel : Label := .inr ()

def sourceProgram (field : Fin 13) : Label → TM2.Stmt Alphabet Label SourceStore
  | .inl label => Inline.statement (τ := Kernel.NatMarshal.Store) Sum.inl doneLabel (BankField.program field label)
  | .inr _ => .halt

def storeIso : SourceStore ≃ Store where
  toFun := fun store => (store.2, (store.1, ()))
  invFun := fun store => (store.2.1, store.1)
  left_inv := by intro store; rcases store with ⟨query, saved⟩; rfl
  right_inv := by intro store; rcases store with ⟨saved, query, marker⟩; cases marker; rfl

def program (field : Fin 13) := StoreIso.machine storeIso (sourceProgram field)

def finished (store : Store) : Store := (store.1, ((none, store.2.1.2), store.2.2))

theorem storeIso_finished (store : Store) :
    storeIso ((none, (storeIso.symm store).1.2), (storeIso.symm store).2) = finished store := by
  rcases store with ⟨saved, query, marker⟩
  cases marker
  rfl

theorem agrees (field : Fin 13) : ∀ label,
    sourceProgram field (.inl label) =
      Inline.statement (τ := Kernel.NatMarshal.Store) Sum.inl doneLabel (BankField.program field label) := by
  intro label; rfl

theorem source_supports (field : Fin 13) : TM2.Supports (sourceProgram field) (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label with
    | inl label =>
      apply Inline.supports_statement Sum.inl doneLabel
        (Finset.univ : Finset BankField.Label) (Finset.univ : Finset Label)
      · intro index _; exact Finset.mem_univ _
      · exact Finset.mem_univ _
      · exact (BankField.supports field).2 label (Finset.mem_univ _)
    | inr marker => cases marker; simp [sourceProgram, TM2.SupportsStmt]

theorem supports (field : Fin 13) : TM2.Supports (program field) (Finset.univ : Finset Label) :=
  StoreIso.supports storeIso (sourceProgram field) (Finset.univ : Finset Label) (source_supports field)

theorem source_runs (field : Fin 13) (value : Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (store : SourceStore)
    (input : contents 0 = encodeCellBits value ++ suffix) (ticks : contents 24 = []) (capture : contents 29 = []) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, store, contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram field) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram field) after = none ∧ after.l = none ∧
      after.var = ((none, store.1.2), store.2) ∧ after.stk = BankField.result field value suffix contents ∧
      run.length ≤ 2 * (encodeCellBits value).length + 11 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    BankField.runs field value suffix contents store.1 input ticks capture
  obtain ⟨returned, after, head, chain, last, label, data, saved, length⟩ :=
    Inline.actual_return_trace Sum.inl doneLabel (BankField.program field) (sourceProgram field)
      (agrees field) source (⟨some BankField.startLabel, store.1, contents⟩ : BankField.State)
      sourceFinal store.2 sourceHead sourceChain sourceLast sourceHalt
  have varExact : after.var = ((none, store.1.2), store.2) := by rw [saved, sourceVar]
  have dataExact : after.stk = BankField.result field value suffix contents := data.trans sourceData
  have afterEq : after = (⟨some doneLabel, ((none, store.1.2), store.2),
      BankField.result field value suffix contents⟩ : SourceState) := by
    rcases after with ⟨currentLabel, currentVar, currentData⟩
    change currentLabel = some doneLabel at label
    change currentVar = ((none, store.1.2), store.2) at varExact
    change currentData = BankField.result field value suffix contents at dataExact
    subst currentLabel; subst currentVar; subst currentData
    rfl
  let final : SourceState := ⟨none, ((none, store.1.2), store.2), BankField.result field value suffix contents⟩
  let run := returned ++ [final]
  have actual : run.IsChain (fun a b => TM2.step (sourceProgram field) a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    rw [afterEq]
    rfl
  refine ⟨run, final, ?_, actual, List.getLast?_append_cons returned final [], rfl, rfl, rfl, rfl, ?_⟩
  · simp only [run, List.head?_append, head, Option.some_or, Inline.cfg,
      Option.map_some, Option.getD_some, startLabel]
  · simp only [run, List.length_append, List.length_cons, List.length_nil]
    omega

/-- The completed real Cell field ends at a true HALT for the parent caller
return adapter. Old bank data remain an explicit suffix until truly cleared. -/
theorem runs (field : Fin 13) (value : Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (store : Store)
    (input : contents 0 = encodeCellBits value ++ suffix) (ticks : contents 24 = []) (capture : contents 29 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program field) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program field) after = none ∧ after.l = none ∧
      after.var = finished store ∧ after.stk = BankField.result field value suffix contents ∧
      run.length ≤ 2 * (encodeCellBits value).length + 11 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    source_runs field value suffix contents (storeIso.symm store) input ticks capture
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso (sourceProgram field) source
      (⟨some startLabel, storeIso.symm store, contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved, sourceVar, storeIso_finished]
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.BankFieldRoot
