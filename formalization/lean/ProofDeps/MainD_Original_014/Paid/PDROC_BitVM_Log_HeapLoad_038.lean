module

public import Paid.PDROC_BitVM_Log_HeapLoad_037

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

@[expose] public section

namespace PDROC.BitVM.Log.HeapLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Actual successful load commit: result28 is copied into the destination
register after old destination bytes are REALLY cleared, then query26 and
result28 are REALLY cleared before the success halt. Old FALSE padding is
data and is charged. No old workspace emptiness is inferred from padding. -/

def copiedResult (destination : Register) (contents : Stack → List Bool) :=
  Function.update contents (registerSlot destination) (contents 28)

def clearedQuery (destination : Register) (contents : Stack → List Bool) :=
  Function.update (copiedResult destination contents) 26 []

def committed (destination : Register) (contents : Stack → List Bool) :=
  Function.update (clearedQuery destination contents) 28 []

theorem copiedResult_work (destination : Register) (contents : Stack → List Bool) :
    copiedResult destination contents 26 = contents 26 ∧ copiedResult destination contents 28 = contents 28 := by
  cases destination <;> simp [copiedResult, registerSlot,
    PaperProofs.Structure.LaminarTree.IndexedRAM.Register.word]

theorem clearedQuery_result (destination : Register) (contents : Stack → List Bool) :
    clearedQuery destination contents 28 = contents 28 := by
  simp only [clearedQuery, Function.update_of_ne (by decide : (28 : Stack) ≠ 26),
    (copiedResult_work destination contents).2]

def commitBudget (destination : Register) (contents : Stack → List Bool) :=
  (contents (registerSlot destination)).length + (contents 26).length + 3 * (contents 28).length + 16

/-- Same actual component paths joined at their real return labels. Entry
found is the actual flag established by the genuine lookup, not a run oracle. -/
theorem commit_runs (pointer destination : Register) (contents : Stack → List Bool) (store : Store)
    (scratch : contents 24 = [])
    (found : (Query.equality store.2.1 && Query.recordTag store.2.1) = true) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some valueBranch, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram pointer destination) after = none ∧
      after.l = none ∧ after.var = (HeapPointer.setTyped (cleared store) true, ()) ∧
      after.stk = committed destination contents ∧ 2 ≤ run.length ∧ run.length ≤ commitBudget destination contents := by
  obtain ⟨copyTrace, copyHead, copyChain, copyLast, copyLength⟩ :=
    transfer_return pointer destination contents store scratch
  obtain ⟨firstTrace, firstHead, firstChain, firstLast, firstLength⟩ :=
    post_return pointer destination 0 (copiedResult destination contents) (cleared store)
  let copyBoundary : SourceState := ⟨some (postLabel 0 0), (cleared store, ()), copiedResult destination contents⟩
  let firstJoined := copyTrace ++ firstTrace.tail
  have firstJoinedHead : firstJoined.head? = some (⟨some (transferLabel 0), (store, ()), contents⟩ : SourceState) := by
    simp only [firstJoined, List.head?_append, copyHead, Option.some_or]
  have firstJoinedChain : firstJoined.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) :=
    TwoStack.join_chain copyTrace firstTrace copyBoundary copyChain firstChain copyLast firstHead
  have firstNotOne : firstTrace.length ≠ 1 := by omega
  have firstJoinedLast : firstJoined.getLast? = some (⟨some (postLabel 1 0),
      (cleared store, ()), clearedQuery destination contents⟩ : SourceState) := by
    simp only [firstJoined, List.getLast?_append, List.getLast?_tail, firstNotOne, ↓reduceIte,
      firstLast, Option.some_or]
    rfl
  obtain ⟨lastTrace, lastHead, lastChain, lastLast, lastLength⟩ :=
    post_return pointer destination 1 (clearedQuery destination contents) (cleared store)
  let queryBoundary : SourceState := ⟨some (postLabel 1 0), (cleared store, ()), clearedQuery destination contents⟩
  let final : SourceState := ⟨none, (HeapPointer.setTyped (cleared store) true, ()), committed destination contents⟩
  let finalPart := lastTrace ++ [final]
  have finalPartHead : finalPart.head? = some queryBoundary := by
    simp only [finalPart, List.head?_append, lastHead, Option.some_or]
    rfl
  have finalPartChain : finalPart.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) := by
    apply lastChain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [lastLast, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    exact done_halt pointer destination (cleared store, ()) (committed destination contents)
  have lastPositive : 0 < lastTrace.length := by omega
  have finalPartNotOne : finalPart.length ≠ 1 := by
    simp only [finalPart, List.length_append, List.length_cons, List.length_nil]
    omega
  have finalPartLast : finalPart.getLast? = some final := List.getLast?_append_cons lastTrace final []
  let committedTrace := firstJoined ++ finalPart.tail
  have committedHead : committedTrace.head? = some (⟨some (transferLabel 0), (store, ()), contents⟩ : SourceState) := by
    simp only [committedTrace, List.head?_append, firstJoinedHead, Option.some_or]
  have committedChain : committedTrace.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) :=
    TwoStack.join_chain firstJoined finalPart queryBoundary firstJoinedChain finalPartChain firstJoinedLast finalPartHead
  have committedLast : committedTrace.getLast? = some final := by
    simp only [committedTrace, List.getLast?_append, List.getLast?_tail, finalPartNotOne, ↓reduceIte,
      finalPartLast, Option.some_or]
  let beforeBranch : SourceState := ⟨some valueBranch, (store, ()), contents⟩
  let run := beforeBranch :: committedTrace
  have head : run.head? = some beforeBranch := rfl
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram pointer destination) a = some b) := by
    apply List.IsChain.cons committedChain
    intro next member
    rw [committedHead] at member
    have equal := Option.mem_some_iff.mp member
    subst next
    exact value_step pointer destination (store, ()) contents found
  have last : run.getLast? = some final := by
    simp only [run, List.getLast?_cons, committedLast, Option.getD_some]
  refine ⟨run, final, head, chain, last, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [run, committedTrace, firstJoined, finalPart, List.length_cons,
      List.length_append, List.length_tail, List.length_nil]
    omega
  · have firstExact : firstTrace.length = (contents 26).length + 3 := by
      change firstTrace.length = (copiedResult destination contents 26).length + 3 at firstLength
      rw [(copiedResult_work destination contents).1] at firstLength
      exact firstLength
    have lastExact : lastTrace.length = (contents 28).length + 3 := by
      change lastTrace.length = (clearedQuery destination contents 28).length + 3 at lastLength
      rw [clearedQuery_result] at lastLength
      exact lastLength
    simp only [run, committedTrace, firstJoined, finalPart, List.length_cons,
      List.length_append, List.length_tail, List.length_nil, commitBudget]
    omega

end PDROC.BitVM.Log.HeapLoad
