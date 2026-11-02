module

public import Paid.PDROC_BitVM_Log_HeapLoad_036

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.Log.HeapLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

/-! The lookup entry representation is PRODUCED by the actual six clears
and Nat pointer read. The same returned path supplies its physical result.
All old nonwork data are carried; lookup status never invents a default Cell. -/

theorem marshalled_fields (query : ℕ) (contents : Stack → List Bool) :
    marshalled query contents 21 = contents 21 ∧
      marshalled query contents 24 = [] ∧ marshalled query contents 25 = [] ∧
      marshalled query contents 26 = encodeNatBits query ∧ marshalled query contents 27 = [] ∧
      marshalled query contents 28 = [] ∧ marshalled query contents 29 = [] := by
  simp [marshalled, preCleared]

theorem lookup_data_shape (events : List HeapEvent) (query : ℕ)
    (contents data : Stack → List Bool)
    (history : contents 21 = encodeHistory events) (work24 : contents 24 = [])
    (work25 : contents 25 = []) (address : contents 26 = encodeNatBits query)
    (work27 : contents 27 = []) (work29 : contents 29 = [])
    (projected : Lift.slots Lookup.heapWorkEmbed data =
      Lookup.slots (encodeHistory events) [] (encodeNatBits query) (Lookup.valueBytes (lookup events query)))
    (frame : ∀ index : Stack, (∀ localIndex, Lookup.heapWorkEmbed localIndex ≠ index) → data index = contents index) :
    data = Function.update contents 28 (Lookup.valueBytes (lookup events query)) := by
  funext index
  by_cases mapped : ∃ localIndex, Lookup.heapWorkEmbed localIndex = index
  · rcases mapped with ⟨localIndex, rfl⟩
    have fact := congrFun projected localIndex
    fin_cases localIndex <;>
      simpa [Lift.slots, Lookup.heapWorkEmbed, Lookup.slots, history, work24, work25, address, work27, work29] using fact
  · have not28 : index ≠ 28 := by
      intro equal
      apply mapped
      refine ⟨5, ?_⟩
      simpa [Lookup.heapWorkEmbed] using equal.symm
    rw [Function.update_of_ne not28]
    exact frame index (fun localIndex equal => mapped ⟨localIndex, equal⟩)

def looked (events : List HeapEvent) (query : ℕ) (contents : Stack → List Bool) :=
  Function.update (marshalled query contents) 28 (Lookup.valueBytes (lookup events query))

def queryBudget (events : List HeapEvent) (query : ℕ) (contents : Stack → List Bool) :=
  clearBudget contents + 2 * (encodeNatBits query).length +
    100 * (events.length + 1) * ((encodeHistory events).length + 1) + 10

/-- A real Nat pointer is copied from its source register, then the actual
latest-first Bool lookup is run. Pointer may later equal destination; it is
not changed anywhere in this prefix. No workspace entry-empty assumption. -/
theorem queried_runs (pointer destination : Register) (events : List HeapEvent) (query : ℕ)
    (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural query))
    (history : contents 21 = encodeHistory events) :
    ∃ (run : List SourceState) (vars : Store),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some (⟨some valueBranch, (vars, ()), looked events query contents⟩ : SourceState) ∧
      vars.1 = (pointerResult (cleared store)).1 ∧
      (Query.equality vars.2.1 && Query.recordTag vars.2.1) = (lookup events query).isSome ∧
      run.length ≤ queryBudget events query contents := by
  obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ :=
    natural_ready pointer destination query contents store register
  let pointerStore := pointerResult (cleared store)
  let pointerContents := marshalled query contents
  have fields := marshalled_fields query contents
  have currentHistory : pointerContents 21 = encodeHistory events := fields.1.trans history
  obtain ⟨right, vars, data, rightHead, rightChain, rightLast, saved, flag, projected, frame, rightLength⟩ :=
    lookup_return pointer destination events query pointerContents pointerStore currentHistory
      fields.2.1 fields.2.2.1 fields.2.2.2.1 fields.2.2.2.2.1 fields.2.2.2.2.2.1 fields.2.2.2.2.2.2
  have dataExact : data = looked events query contents :=
    lookup_data_shape events query pointerContents data currentHistory fields.2.1 fields.2.2.1
      fields.2.2.2.1 fields.2.2.2.2.1 fields.2.2.2.2.2.2 projected frame
  let boundary : SourceState := ⟨some typeBranch, (pointerStore, ()), pointerContents⟩
  let body := boundary :: right
  have bodyHead : body.head? = some boundary := rfl
  have bodyChain : body.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) := by
    apply List.IsChain.cons rightChain
    intro next member
    rw [rightHead] at member
    have equal := Option.mem_some_iff.mp member
    subst next
    exact type_step pointer destination (pointerStore, ()) pointerContents rfl
  have bodyLast : body.getLast? = some (⟨some valueBranch, (vars, ()), looked events query contents⟩ : SourceState) := by
    simp only [body, List.getLast?_cons, rightLast, Option.getD_some, dataExact]
  have rightPositive : 0 < right.length := by
    cases right with
    | nil => simp only [List.head?_nil, reduceCtorEq] at rightHead
    | cons first rest => simp only [List.length_cons]; omega
  have bodyNotOne : body.length ≠ 1 := by simp only [body, List.length_cons]; omega
  let run := left ++ body.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, leftHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) :=
    TwoStack.join_chain left body boundary leftChain bodyChain leftLast bodyHead
  have last : run.getLast? = some (⟨some valueBranch, (vars, ()), looked events query contents⟩ : SourceState) := by
    simp only [run, List.getLast?_append, List.getLast?_tail, bodyNotOne, ↓reduceIte,
      bodyLast, Option.some_or]
  refine ⟨run, vars, head, chain, last, saved, flag, ?_⟩
  simp only [run, body, List.length_append, List.length_tail, List.length_cons, queryBudget]
  omega

end PDROC.BitVM.Log.HeapLoad
