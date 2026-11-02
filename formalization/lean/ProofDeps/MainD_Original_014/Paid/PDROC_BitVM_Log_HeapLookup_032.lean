module

public import Paid.PDROC_BitVM_Log_HeapTransfer_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.Log.HeapLookup

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native

/-! Store adapter around the SAME actual32-stack lookup. Caller pointer
flags are a fixed finite product factor; they are not addresses or values.
All55 labels and108 finite store states are chosen before the input. -/

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Lookup.Label ⊕ Unit
abbrev SourceStore := Lookup.Store × Kernel.NatMarshal.Store
abbrev Store := HeapPointer.Store
abbrev SourceState := TM2.Cfg Alphabet Label SourceStore
abbrev State := TM2.Cfg Alphabet Label Store

def startLabel : Label := .inl Lookup.gateLabel
def doneLabel : Label := .inr ()
def sourceProgram : Label → TM2.Stmt Alphabet Label SourceStore
  | .inl label => Inline.statement (τ := Kernel.NatMarshal.Store) Sum.inl doneLabel (Lookup.wideProgram label)
  | .inr _ => .halt
def storeIso : SourceStore ≃ Store := Equiv.prodComm _ _
def program := StoreIso.machine storeIso sourceProgram

theorem agrees : ∀ label,
    sourceProgram (.inl label) = Inline.statement (τ := Kernel.NatMarshal.Store) Sum.inl doneLabel (Lookup.wideProgram label) := by
  intro label; rfl

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  apply StoreIso.supports storeIso sourceProgram (Finset.univ : Finset Label)
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label with
    | inl label =>
      apply Inline.supports_statement Sum.inl doneLabel (Finset.univ : Finset Lookup.Label) (Finset.univ : Finset Label)
      · intro index _; exact Finset.mem_univ _
      · exact Finset.mem_univ _
      · exact Lookup.wide_supports.2 label (Finset.mem_univ _)
    | inr label => cases label; simp [sourceProgram, TM2.SupportsStmt]

theorem representation (events : List HeapEvent) (query : ℕ) (contents : Stack → List Bool) (store : Lookup.Store)
    (history : contents 21 = encodeHistory events) (work24 : contents 24 = [])
    (work25 : contents 25 = []) (address : contents 26 = encodeNatBits query)
    (work27 : contents 27 = []) (work28 : contents 28 = []) (work29 : contents 29 = []) :
    Lift.cfg Lookup.heapWorkEmbed (⟨some Lookup.gateLabel, store, contents⟩ : Lookup.WideState) =
      Lookup.state (some Lookup.gateLabel) store (encodeHistory events) [] (encodeNatBits query) [] := by
  have data : Lift.slots Lookup.heapWorkEmbed contents = Lookup.slots (encodeHistory events) [] (encodeNatBits query) [] := by
    funext index
    fin_cases index
    · exact history
    · exact work24
    · exact work25
    · exact address
    · exact work27
    · exact work28
    · exact work29
  exact congrArg (fun current => (⟨some Lookup.gateLabel, store, current⟩ : Lookup.State)) data

/-- Source path in the reordered finite caller store. History/query are real
stack data; all working emptiness premises are produced by actual clear code. -/
theorem source_runs (events : List HeapEvent) (query : ℕ) (contents : Stack → List Bool) (store : SourceStore)
    (history : contents 21 = encodeHistory events) (work24 : contents 24 = [])
    (work25 : contents 25 = []) (address : contents 26 = encodeNatBits query)
    (work27 : contents 27 = []) (work28 : contents 28 = []) (work29 : contents 29 = []) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, store, contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step sourceProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step sourceProgram after = none ∧ after.l = none ∧
      after.var.2 = store.2 ∧
      (Query.equality after.var.1.1 && Query.recordTag after.var.1.1) = (lookup events query).isSome ∧
      Lift.slots Lookup.heapWorkEmbed after.stk = Lookup.slots (encodeHistory events) [] (encodeNatBits query)
        (Lookup.valueBytes (lookup events query)) ∧
      (∀ index : Stack, (∀ localIndex, Lookup.heapWorkEmbed localIndex ≠ index) → after.stk index = contents index) ∧
      run.length ≤ 100 * (events.length + 1) * ((encodeHistory events).length + 1) + 1 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceData, sourceFlag, sourceFrame, sourceLength⟩ :=
    Lookup.wide_lookup_runs events query [] store.1
      (⟨some Lookup.gateLabel, store.1, contents⟩ : Lookup.WideState)
      (representation events query contents store.1 history work24 work25 address work27 work28 work29)
  obtain ⟨returned, after, head, chain, last, returnedLabel, data, saved, length⟩ :=
    Inline.actual_return_trace Sum.inl doneLabel Lookup.wideProgram sourceProgram agrees source
      (⟨some Lookup.gateLabel, store.1, contents⟩ : Lookup.WideState) sourceFinal store.2
      sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (sourceFinal.var, store.2) := saved
  have finalData : after.stk = sourceFinal.stk := data
  have afterEq : after = (⟨some doneLabel, (sourceFinal.var, store.2), sourceFinal.stk⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some doneLabel at returnedLabel
    change vars = (sourceFinal.var, store.2) at finalVar
    change current = sourceFinal.stk at finalData
    subst label; subst vars; subst current
    rfl
  let final : SourceState := ⟨none, (sourceFinal.var, store.2), sourceFinal.stk⟩
  let run := returned ++ [final]
  have actual : run.IsChain (fun a b => TM2.step sourceProgram a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    rw [afterEq]
    rfl
  have entry : returned.head? = some (⟨some startLabel, store, contents⟩ : SourceState) := head
  refine ⟨run, final, ?_, actual, List.getLast?_append_cons returned final [], rfl, rfl,
    rfl, sourceFlag, ?_, sourceFrame, ?_⟩
  · change (returned ++ [final]).head? = some (⟨some startLabel, store, contents⟩ : SourceState)
    simp only [List.head?_append, entry, Option.some_or]
  · simpa only [List.append_nil] using sourceData
  · simp only [run, List.length_append, List.length_cons, List.length_nil]
    omega

/-- ONE path of the genuine log lookup in the heap opcode's108 flag store.
Absent/tombstoned addresses return false and [] on actual result28. -/
theorem runs (events : List HeapEvent) (query : ℕ) (contents : Stack → List Bool) (store : Store)
    (history : contents 21 = encodeHistory events) (work24 : contents 24 = [])
    (work25 : contents 25 = []) (address : contents 26 = encodeNatBits query)
    (work27 : contents 27 = []) (work28 : contents 28 = []) (work29 : contents 29 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧ after.l = none ∧
      after.var.1 = store.1 ∧
      (Query.equality after.var.2.1 && Query.recordTag after.var.2.1) = (lookup events query).isSome ∧
      Lift.slots Lookup.heapWorkEmbed after.stk = Lookup.slots (encodeHistory events) [] (encodeNatBits query)
        (Lookup.valueBytes (lookup events query)) ∧
      (∀ index : Stack, (∀ localIndex, Lookup.heapWorkEmbed localIndex ≠ index) → after.stk index = contents index) ∧
      run.length ≤ 100 * (events.length + 1) * ((encodeHistory events).length + 1) + 1 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceSaved, sourceFlag, sourceData, sourceFrame, sourceLength⟩ :=
    source_runs events query contents (storeIso.symm store) history work24 work25 address work27 work28 work29
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso sourceProgram source
      (⟨some startLabel, storeIso.symm store, contents⟩ : SourceState) sourceFinal
      sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, ?_, ?_, ?_, ?_⟩
  · rw [saved]; exact sourceSaved
  · rw [saved]; exact sourceFlag
  · rw [data]; exact sourceData
  · intro index outside
    rw [data]
    exact sourceFrame index outside
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.HeapLookup
