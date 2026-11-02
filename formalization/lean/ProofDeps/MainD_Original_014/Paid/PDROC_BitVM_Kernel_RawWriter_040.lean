module

public import Paid.PDROC_BitVM_Kernel_RawCell_039

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawWrite

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

def inputSize (target : Register) (contents : Stack → List Bool) : ℕ :=
  (contents 0).length+(contents 24).length+(contents 25).length+(contents 29).length+
    (contents (registerSlot target)).length

/-- A whole canonical Cell replacement on ONE actual path. Every old
target/native-left/capture byte and all real input/archive padding are
cleared by code; there is no caller-empty workspace premise. -/
theorem runs (target : Register) (value : Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (saved : ResultCell.Store)
    (input : contents 0=encodeCellBits value++suffix) :
    ∃ (run : List State) (final : State),
      run.head?=some (before contents saved) ∧
      run.IsChain (fun a b=>TM2.step (program target) a=some b) ∧
      run.getLast?=some final ∧ TM2.step (program target) final=none ∧
      final.stk (registerSlot target)=encodeCellBits value ∧
      final.stk 0=[] ∧ final.stk 24=[] ∧ final.stk 25=[] ∧ final.stk 29=[] ∧
      run.length ≤ 64*(inputSize target contents+1) ∧
      ∀ role,role ≠ 0 → role ≠ 24 → role ≠ 25 → role ≠ 29 → role ≠ registerSlot target →
        final.stk role=contents role := by
  have not0 : (0 : Stack) ≠ registerSlot target := by cases target <;> decide
  have not24 : (24 : Stack) ≠ registerSlot target := by cases target <;> decide
  have not25 : (25 : Stack) ≠ registerSlot target := by cases target <;> decide
  have not29 : (29 : Stack) ≠ registerSlot target := by cases target <;> decide
  obtain ⟨first,ready,firstHead,firstChain,firstLast,readyLabel,readyStore,readyData,firstTime⟩ :=
    prepare_runs target contents saved
  have ready0 : ready.stk 0=contents 0 := by
    rw [readyData]
    simp only [preparedContents,Function.update_of_ne not0,
      Function.update_of_ne (by decide : (0 : Stack) ≠ 29),Function.update_of_ne (by decide : (0 : Stack) ≠ 24)]
  have ready24 : ready.stk 24=[] := by
    rw [readyData]
    simp only [preparedContents,Function.update_of_ne not24,
      Function.update_of_ne (by decide : (24 : Stack) ≠ 29),Function.update_self]
  have ready29 : ready.stk 29=[] := by
    rw [readyData]
    simp only [preparedContents,Function.update_of_ne not29,Function.update_self]
  have readyTarget : ready.stk (registerSlot target)=[] := by
    rw [readyData]
    change Function.update (Function.update (Function.update contents 24 []) 29 []) (registerSlot target) [] (registerSlot target)=[]
    exact Function.update_self _ _ _
  have ready25 : ready.stk 25=contents 25 := by
    rw [readyData]
    simp only [preparedContents,Function.update_of_ne not25,
      Function.update_of_ne (by decide : (25 : Stack) ≠ 29),Function.update_of_ne (by decide : (25 : Stack) ≠ 24)]
  obtain ⟨second,written,secondHead,secondChain,secondLast,writtenLabel,writtenStore,word,remaining,
    empty24,empty29,secondTime,cellFrame,archive⟩ :=
    cell_call target value suffix ready.stk saved none (ready0.trans input) ready24 ready29 readyTarget
  have cellBoundary : cellCfg none (ResultCell.before ready.stk saved)=ready := by
    rcases ready with ⟨label,finiteStore,physical⟩
    change label=some cellStart at readyLabel
    change finiteStore=(none,saved) at readyStore
    subst label
    subst finiteStore
    rfl
  rw [cellBoundary] at secondHead
  have joined := PDROC.BitVM.Log.TwoStack.join_chain first second ready
    firstChain secondChain firstLast secondHead
  have joinedLast := join_last first second ready written firstLast secondHead secondLast
  obtain ⟨third,cleared,thirdHead,thirdChain,thirdLast,clearedLabel,clearedStore,clearedData,thirdTime⟩ :=
    clear_call target 3 written.stk none (none,saved.2)
  have writtenCanonical : written=⟨some (clearLabel 3),(none,(none,saved.2)),written.stk⟩ :=
    state_of_fields written _ _ writtenLabel writtenStore
  rw [← writtenCanonical] at thirdHead
  have joined' := PDROC.BitVM.Log.TwoStack.join_chain (first++second.tail) third written
    joined thirdChain joinedLast thirdHead
  have joinedLast' := join_last (first++second.tail) third written cleared joinedLast thirdHead thirdLast
  obtain ⟨fourth,returned,fourthHead,fourthChain,fourthLast,returnedLabel,_returnedStore,returnedData,fourthTime⟩ :=
    clear_call target 4 cleared.stk none (none,saved.2)
  have clearedCanonical : cleared=⟨some (clearLabel 4),(none,(none,saved.2)),cleared.stk⟩ :=
    state_of_fields cleared _ _ clearedLabel clearedStore
  rw [← clearedCanonical] at fourthHead
  let joinedRun := ((first++second.tail)++third.tail)++fourth.tail
  have joinedChain : joinedRun.IsChain (fun a b=>TM2.step (program target) a=some b) :=
    PDROC.BitVM.Log.TwoStack.join_chain ((first++second.tail)++third.tail) fourth cleared
      joined' fourthChain joinedLast' fourthHead
  have joinedEnd : joinedRun.getLast?=some returned :=
    join_last ((first++second.tail)++third.tail) fourth cleared returned joinedLast' fourthHead fourthLast
  let final : State := ⟨none,returned.var,returned.stk⟩
  have lastEdge : TM2.step (program target) returned=some final := by
    rcases returned with ⟨label,finiteStore,physical⟩
    change label=some doneLabel at returnedLabel
    subst label
    rfl
  have lastPair : [returned,final].IsChain (fun a b=>TM2.step (program target) a=some b) :=
    List.isChain_cons_cons.mpr ⟨lastEdge,List.isChain_singleton _⟩
  have actual := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain
    joinedRun returned [final] joinedEnd joinedChain lastPair
  have finalData : final.stk=Function.update (Function.update written.stk 0 []) 25 [] := by
    change returned.stk=_
    rw [returnedData,clearedData]
    rfl
  have thirdFee : (written.stk (clearRole target 3)).length=suffix.length := congrArg List.length remaining
  have fourthFee : (cleared.stk (clearRole target 4)).length=
      (encodeCellBits value).length+(contents 25).length := by
    rw [clearedData]
    change (Function.update written.stk 0 [] 25).length=_
    rw [Function.update_of_ne (by decide : (25 : Stack) ≠ 0),archive,ready25,List.length_append,List.length_reverse]
  have inputLength : (contents 0).length=(encodeCellBits value).length+suffix.length := by
    rw [input,List.length_append]
  refine ⟨joinedRun++[final],final,?_,actual,List.getLast?_append_cons joinedRun final [],rfl,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [joinedRun,List.head?_append,firstHead,Option.some_or]
  · rw [finalData,Function.update_of_ne not25.symm,Function.update_of_ne not0.symm]
    exact word
  · rw [finalData,Function.update_of_ne (by decide : (0 : Stack) ≠ 25),Function.update_self]
  · rw [finalData,Function.update_of_ne (by decide : (24 : Stack) ≠ 25),
      Function.update_of_ne (by decide : (24 : Stack) ≠ 0)]
    exact empty24
  · rw [finalData,Function.update_self]
  · rw [finalData,Function.update_of_ne (by decide : (29 : Stack) ≠ 25),
      Function.update_of_ne (by decide : (29 : Stack) ≠ 0)]
    exact empty29
  · rw [thirdFee] at thirdTime
    rw [fourthFee] at fourthTime
    simp only [joinedRun,List.length_append,List.length_tail,List.length_cons,List.length_nil]
    dsimp only [inputSize]
    omega
  · intro role outside0 outside24 outside25 outside29 outsideTarget
    rw [finalData,Function.update_of_ne outside25,Function.update_of_ne outside0,
      cellFrame role outside0 outside25 outside29 outsideTarget,readyData]
    simp only [preparedContents,Function.update_of_ne outsideTarget,
      Function.update_of_ne outside29,Function.update_of_ne outside24]

end PDROC.BitVM.Kernel.RawWrite
