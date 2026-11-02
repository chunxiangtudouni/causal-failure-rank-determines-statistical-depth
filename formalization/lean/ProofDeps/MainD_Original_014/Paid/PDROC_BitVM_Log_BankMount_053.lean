module

public import Paid.PDROC_BitVM_Log_BankMount_052

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.BankMount

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! Actual TRUE footer, actual work cleanup and actual final HALT. This
changes the field-loop boundary invariant: the footer has now been consumed,
so the old FieldData.input is deliberately NOT asserted of the final state. -/

def footerStore (store : Store) : Store := ((some true, store.1.2), store.2)
def footerData (suffix : List Bool) (contents : Stack → List Bool) := Function.update contents 0 suffix
def clean24 (suffix : List Bool) (contents : Stack → List Bool) := Function.update (footerData suffix contents) 24 []
def clean25 (suffix : List Bool) (contents : Stack → List Bool) := Function.update (clean24 suffix contents) 25 []
def finishData (suffix : List Bool) (contents : Stack → List Bool) := Function.update (clean25 suffix contents) 29 []

structure Mounted (basis : Stack → List Bool) (cells : List Cell) (suffix : List Bool)
    (contents : Stack → List Bool) : Prop where
  input : contents 0 = suffix
  work : contents 24 = [] ∧ contents 25 = [] ∧ contents 29 = []
  banks : ∀ field : Fin 13, contents (BankDrain.bankSlot field) = bankWords cells field
  frame : ∀ index : Stack, Outside index → contents index = basis index

theorem FieldData.mounted {core : Bool} {basis contents : Stack → List Bool} {cells : List Cell} {suffix : List Bool}
    (ready : FieldData core basis cells [] suffix contents) : Mounted basis cells suffix (finishData suffix contents) := by
  constructor
  · simp [finishData, clean25, clean24, footerData]
  · simp [finishData, clean25, clean24, footerData]
  · intro field
    have not0 := BankDrain.bankSlot_ne field 0 (by decide)
    have not24 := BankDrain.bankSlot_ne field 24 (by decide)
    have not25 := BankDrain.bankSlot_ne field 25 (by decide)
    have not29 := BankDrain.bankSlot_ne field 29 (by decide)
    simp only [finishData, clean25, clean24, footerData, Function.update_of_ne not29,
      Function.update_of_ne not25, Function.update_of_ne not24, Function.update_of_ne not0]
    exact ready.banks field
  · intro index outside
    have not0 : index ≠ 0 := by intro equal; subst index; norm_num [Outside] at outside
    simp only [finishData, clean25, clean24, footerData, Function.update_of_ne outside.2.2.2,
      Function.update_of_ne outside.2.2.1, Function.update_of_ne outside.2.1, Function.update_of_ne not0]
    exact ready.frame index outside

theorem footer_data_step (core : Bool) (store : Store) (suffix : List Bool) (contents : Stack → List Bool)
    (input : contents 0 = true :: suffix) :
    TM2.step (sourceProgram core) (⟨some footerLabel, (store, ()), contents⟩ : SourceState) =
      some (⟨some (cleanLabel 0 0), (footerStore store, ()), footerData suffix contents⟩ : SourceState) := by
  have restored : Function.update contents 0 (true :: suffix) = contents := by
    funext index
    by_cases here : index = 0
    · subst index; rw [Function.update_self]; exact input.symm
    · rw [Function.update_of_ne here]
  simpa only [restored, footerData, footerStore, saveFooter] using footer_step core (store, ()) suffix contents

theorem finish_runs (core : Bool) (basis : Stack → List Bool) (cells : List Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (store : Store) (ready : FieldData core basis cells [] suffix contents) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some footerLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram core) after = none ∧ after.l = none ∧
      Query.equality after.var.1.2.1 = true ∧ Mounted basis cells suffix after.stk ∧
      2 ≤ run.length ∧ run.length ≤ (contents 25).length + 20 := by
  let saved := HeapLoad.cleared (footerStore store)
  obtain ⟨firstTrace, firstHead, firstChain, firstLast, firstLength⟩ :=
    clean_return core 0 (footerData suffix contents) (footerStore store)
  have actualInput : contents 0 = true :: suffix := by
    simpa only [List.flatMap_nil, List.nil_append] using ready.input
  let beforeFooter : SourceState := ⟨some footerLabel, (store, ()), contents⟩
  let firstPart := beforeFooter :: firstTrace
  have firstPartHead : firstPart.head? = some beforeFooter := rfl
  have firstPartChain : firstPart.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) := by
    apply List.IsChain.cons firstChain
    intro next member
    rw [firstHead] at member
    have equal := Option.mem_some_iff.mp member
    subst next
    exact footer_data_step core store suffix contents actualInput
  have firstPartLast : firstPart.getLast? = some (⟨some (cleanLabel 1 0), (saved, ()), clean24 suffix contents⟩ : SourceState) := by
    simp only [firstPart, List.getLast?_cons, firstLast, Option.getD_some]
    rfl
  obtain ⟨secondTrace, secondHead, secondChain, secondLast, secondLength⟩ :=
    clean_return core 1 (clean24 suffix contents) saved
  let middle : SourceState := ⟨some (cleanLabel 1 0), (saved, ()), clean24 suffix contents⟩
  let left := firstPart ++ secondTrace.tail
  have leftHead : left.head? = some beforeFooter := by
    simp only [left, List.head?_append, firstPartHead, Option.some_or]
  have leftChain : left.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) :=
    TwoStack.join_chain firstPart secondTrace middle firstPartChain secondChain firstPartLast secondHead
  have secondNotOne : secondTrace.length ≠ 1 := by omega
  have leftLast : left.getLast? = some (⟨some (cleanLabel 2 0), (saved, ()), clean25 suffix contents⟩ : SourceState) := by
    simp only [left, List.getLast?_append, List.getLast?_tail, secondNotOne, ↓reduceIte, secondLast, Option.some_or]
    rfl
  obtain ⟨thirdTrace, thirdHead, thirdChain, thirdLast, thirdLength⟩ := clean_return core 2 (clean25 suffix contents) saved
  let final : SourceState := ⟨none, (HeapPointer.setTyped saved true, ()), finishData suffix contents⟩
  let right := thirdTrace ++ [final]
  have rightHead : right.head? = some (⟨some (cleanLabel 2 0), (saved, ()), clean25 suffix contents⟩ : SourceState) := by
    simp only [right, List.head?_append, thirdHead, Option.some_or]
  have rightChain : right.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) := by
    apply thirdChain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [thirdLast, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    exact done_halt core (saved, ()) (finishData suffix contents)
  have thirdPositive : 0 < thirdTrace.length := by omega
  have rightNotOne : right.length ≠ 1 := by
    simp only [right, List.length_append, List.length_cons, List.length_nil]
    omega
  have rightLast : right.getLast? = some final := List.getLast?_append_cons thirdTrace final []
  let run := left ++ right.tail
  have head : run.head? = some beforeFooter := by
    simp only [run, List.head?_append, leftHead, Option.some_or]
  let lastBoundary : SourceState := ⟨some (cleanLabel 2 0), (saved, ()), clean25 suffix contents⟩
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) :=
    TwoStack.join_chain left right lastBoundary leftChain rightChain leftLast rightHead
  have last : run.getLast? = some final := by
    simp only [run, List.getLast?_append, List.getLast?_tail, rightNotOne, ↓reduceIte, rightLast, Option.some_or]
  refine ⟨run, final, head, chain, last, rfl, rfl, rfl, ready.mounted, ?_, ?_⟩
  · simp only [run, left, firstPart, right, List.length_append, List.length_cons, List.length_tail, List.length_nil]
    omega
  · have firstExact : firstTrace.length = 3 := by
      simpa [cleanSlot, footerData, ready.ticks] using firstLength
    have secondExact : secondTrace.length = (contents 25).length + 3 := by
      simpa [cleanSlot, clean24, footerData] using secondLength
    have thirdExact : thirdTrace.length = 3 := by
      simpa [cleanSlot, clean25, clean24, footerData, ready.capture] using thirdLength
    simp only [run, left, firstPart, right, List.length_append, List.length_cons, List.length_tail, List.length_nil]
    omega

end PDROC.BitVM.Log.BankMount
