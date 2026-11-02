module

public import Paid.PDROC_BitVM_Log_Query_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.BitVM.Log.Query

open Turing

/-- One actual path initializes the equality bit, compares every address Bool,
restores the query using actual drains, and executes the real final halt. The
List equality occurs only in the proved result, not in the transition code. -/
theorem word_compare_runs (address query : List Bool) (other : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some 0) store address query [] other) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧ equality after.var = decide (address = query) ∧
      recordTag after.var = recordTag store ∧ after.stk = slots [] query [] other ∧
      run.length ≤ 2 * address.length + 5 := by
  let initialStore := setEquality store true
  let finishStore := afterStore address query initialStore
  let first := state (some 0) store address query [] other
  let compared := state (some 2) finishStore [] (query.drop address.length)
    (query.take address.length).reverse other
  let left := first :: loopTrace other address query [] initialStore
  have leftHead : left.head? = some first := rfl
  have leftChain : left.IsChain (fun a b => TM2.step program a = some b) := by
    apply List.IsChain.cons (loop_trace_chain address query [] other initialStore)
    intro after member
    rw [loop_trace_head] at member
    have equal := Option.mem_some_iff.mp member
    subst after
    exact initialize_step (slots address query [] other) store
  have leftLast : left.getLast? = some compared := by
    simp only [left, List.getLast?_cons, loop_trace_last, List.append_nil, Option.getD_some]
    rfl
  have leftLength : left.length = address.length + 3 := by
    simp only [left, List.length_cons, loop_trace_length]
  obtain ⟨right, rightHead, rightChain, rightLast, rightLength⟩ :=
    restore_run (query.drop address.length) (query.take address.length).reverse other finishStore
  have restoredWord : (query.take address.length).reverse.reverse ++ query.drop address.length = query := by
    rw [List.reverse_reverse, List.take_append_drop]
  rw [restoredWord] at rightLast
  let joined := left ++ right.tail
  let ready := state (some 3) (none, finishStore.2) [] query [] other
  let after := state none (none, finishStore.2) [] query [] other
  have joinedHead : joined.head? = some first := by
    simp only [joined, List.head?_append, leftHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step program a = some b) :=
    TwoStack.join_chain left right compared leftChain rightChain leftLast rightHead
  have rightNotOne : right.length ≠ 1 := by omega
  have joinedLast : joined.getLast? = some ready := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, rightNotOne,
      ↓reduceIte, rightLast, Option.some_or]
    rfl
  let run := joined ++ [after]
  have runChain : run.IsChain (fun a b => TM2.step program a = some b) := by
    apply joinedChain.append (List.isChain_singleton _)
    intro before hb next hn
    simp only [joinedLast, Option.mem_some_iff] at hb
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst before
    subst next
    exact final_halt (slots [] query [] other) (none, finishStore.2)
  refine ⟨run, after, ?_, runChain, ?_, ?_, rfl, ?_, ?_, rfl, ?_⟩
  · change (joined ++ [after]).head? = some first
    simp only [List.head?_append, joinedHead, Option.some_or]
  · exact List.getLast?_append_cons joined after []
  · exact final_halted (slots [] query [] other) (none, finishStore.2)
  · simp [after, state, finishStore, initialStore, afterStore, equality, setEquality]
  · simp [after, state, finishStore, initialStore, afterStore, recordTag, setEquality]
  · simp only [run, joined, List.length_append, List.length_cons, List.length_nil,
      List.length_tail, leftLength]
    simp only [List.length_reverse, List.length_take] at rightLength
    have taken := Nat.min_le_left address.length query.length
    omega

end PDROC.BitVM.Log.Query
