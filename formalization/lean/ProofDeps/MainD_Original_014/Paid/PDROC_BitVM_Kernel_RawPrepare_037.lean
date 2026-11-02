module

public import Paid.PDROC_BitVM_Kernel_RawClear_036

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawWrite

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

theorem state_of_fields (source : State) (label : Option Label) (saved : Store)
    (labelEq : source.l=label) (storeEq : source.var=saved) :
    source=⟨label,saved,source.stk⟩ := by
  rcases source with ⟨actualLabel,actualStore,contents⟩
  change actualLabel=label at labelEq
  change actualStore=saved at storeEq
  subst actualLabel
  subst actualStore
  rfl

theorem join_last (first second : List State) (middle final : State)
    (firstLast : first.getLast?=some middle) (secondHead : second.head?=some middle)
    (secondLast : second.getLast?=some final) :
    (first++second.tail).getLast?=some final := by
  cases second with
  | nil => simp only [List.head?_nil,reduceCtorEq] at secondHead
  | cons start rest =>
    have same : start=middle := Option.some.inj secondHead
    subst start
    cases rest with
    | nil =>
      have same : middle=final := Option.some.inj secondLast
      simpa only [List.tail_cons,List.append_nil,same] using firstLast
    | cons next later =>
      rw [List.tail_cons,List.getLast?_append_cons]
      simpa only [List.getLast?_cons_cons] using secondLast

def preparedContents (target : Register) (contents : Stack → List Bool) :=
  Function.update (Function.update (Function.update contents 24 []) 29 []) (registerSlot target) []

/-- Actual three-clear producer for the result parser. It removes all
old native-left FALSE/TRUE cells, old capture and destination bytes. The
input Cell and arbitrary archive are left in their physical locations. -/
theorem prepare_runs (target : Register) (contents : Stack → List Bool) (saved : ResultCell.Store) :
    ∃ (run : List State) (ready : State),
      run.head?=some (before contents saved) ∧
      run.IsChain (fun a b=>TM2.step (program target) a=some b) ∧
      run.getLast?=some ready ∧ ready.l=some cellStart ∧ ready.var=(none,saved) ∧
      ready.stk=preparedContents target contents ∧
      run.length ≤ (contents 24).length+(contents 29).length+(contents (registerSlot target)).length+4 := by
  obtain ⟨first,firstLast,firstHead,firstChain,firstEnd,firstLabel,firstStore,firstData,firstTime⟩ :=
    clear_call target 0 contents none saved
  obtain ⟨second,secondLast,secondHead,secondChain,secondEnd,secondLabel,secondStore,secondData,secondTime⟩ :=
    clear_call target 1 firstLast.stk none saved
  have firstCanonical : firstLast=⟨some (clearLabel 1),(none,saved),firstLast.stk⟩ :=
    state_of_fields firstLast _ _ firstLabel firstStore
  rw [← firstCanonical] at secondHead
  have firstJoin := PDROC.BitVM.Log.TwoStack.join_chain first second firstLast
    firstChain secondChain firstEnd secondHead
  have firstJoinLast := join_last first second firstLast secondLast firstEnd secondHead secondEnd
  obtain ⟨third,ready,thirdHead,thirdChain,thirdEnd,thirdLabel,thirdStore,thirdData,thirdTime⟩ :=
    clear_call target 2 secondLast.stk none saved
  have secondCanonical : secondLast=⟨some (clearLabel 2),(none,saved),secondLast.stk⟩ :=
    state_of_fields secondLast _ _ secondLabel secondStore
  rw [← secondCanonical] at thirdHead
  have actual := PDROC.BitVM.Log.TwoStack.join_chain (first++second.tail) third secondLast
    firstJoin thirdChain firstJoinLast thirdHead
  have actualLast := join_last (first++second.tail) third secondLast ready firstJoinLast thirdHead thirdEnd
  have data : ready.stk=preparedContents target contents := by
    rw [thirdData,secondData,firstData]
    rfl
  have targetNot24 : registerSlot target ≠ 24 := by cases target <;> decide
  have targetNot29 : registerSlot target ≠ 29 := by cases target <;> decide
  have secondFee : (firstLast.stk (clearRole target 1)).length=(contents 29).length := by
    rw [firstData]
    change (Function.update contents 24 [] 29).length=_
    rw [Function.update_of_ne (by decide : (29 : Stack) ≠ 24)]
  have thirdFee : (secondLast.stk (clearRole target 2)).length=(contents (registerSlot target)).length := by
    rw [secondData,firstData]
    change (Function.update (Function.update contents 24 []) 29 [] (registerSlot target)).length=_
    rw [Function.update_of_ne targetNot29,Function.update_of_ne targetNot24]
  refine ⟨(first++second.tail)++third.tail,ready,?_,actual,actualLast,thirdLabel,thirdStore,data,?_⟩
  · simp only [List.head?_append,firstHead,Option.some_or]
    rfl
  · rw [secondFee] at secondTime
    rw [thirdFee] at thirdTime
    change first.length=(contents 24).length+2 at firstTime
    simp only [List.length_append,List.length_tail]
    omega

end PDROC.BitVM.Kernel.RawWrite
