module

public import Paid.PDROC_BitVM_Log_Capture_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.BitVM.Log.Capture

open Turing

/-- One selected actual capture/normalize/halt run. It archives the original
field and produces its normal-order bytes on workstack1 for real comparison. -/
theorem capture_runs (digits suffix archive : List Bool) (other : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some 0) store (Header.natWord digits ++ suffix) [] archive [] other) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧ after.var = (none, store.2) ∧
      after.stk = slots suffix (Header.natWord digits)
        ((Header.natWord digits).reverse ++ archive) [] other ∧
      run.length = 4 * digits.length + 6 := by
  let frontTrace := scanTrace digits suffix archive [] other store
  let beforeNormalize := state (some 2) (Query.setRecord store none) suffix []
    ((Header.natWord digits).reverse ++ archive) (Header.natWord digits).reverse other
  have prefixHead : frontTrace.head? = some (state (some 0) store
      (Header.natWord digits ++ suffix) [] archive [] other) :=
    scan_trace_head digits suffix archive [] other store
  have prefixChain : frontTrace.IsChain (fun a b => TM2.step program a = some b) :=
    scan_trace_chain digits suffix archive [] other store
  have prefixLast : frontTrace.getLast? = some beforeNormalize := by
    simpa only [frontTrace, List.append_nil] using scan_trace_last digits suffix archive [] other store
  have prefixLength : frontTrace.length = 2 * digits.length + 3 :=
    scan_trace_length digits suffix archive [] other store
  obtain ⟨normal, normalHead, normalChain, normalLast, normalLength⟩ :=
    normalize_run suffix ((Header.natWord digits).reverse ++ archive)
      (Header.natWord digits).reverse other (Query.setRecord store none)
  rw [List.reverse_reverse] at normalLast
  let ready := state (some 3) (none, store.2) suffix (Header.natWord digits)
    ((Header.natWord digits).reverse ++ archive) [] other
  let after := state none (none, store.2) suffix (Header.natWord digits)
    ((Header.natWord digits).reverse ++ archive) [] other
  let joined := frontTrace ++ normal.tail
  have joinedHead : joined.head? = frontTrace.head? := by
    simp only [joined, List.head?_append, prefixHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step program a = some b) :=
    TwoStack.join_chain frontTrace normal beforeNormalize prefixChain normalChain prefixLast normalHead
  have normalNotOne : normal.length ≠ 1 := by omega
  have joinedLast : joined.getLast? = some ready := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, normalNotOne,
      ↓reduceIte, normalLast, Option.some_or]
    rfl
  let run := joined ++ [after]
  have runChain : run.IsChain (fun a b => TM2.step program a = some b) := by
    apply joinedChain.append (List.isChain_singleton _)
    intro before hb next hn
    simp only [joinedLast, Option.mem_some_iff] at hb
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst before
    subst next
    rfl
  refine ⟨run, after, ?_, runChain, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · change (joined ++ [after]).head? = _
    simp only [List.head?_append, joinedHead, prefixHead, Option.some_or]
  · exact List.getLast?_append_cons joined after []
  · have wordLength : (Header.natWord digits).length = 2 * digits.length + 1 := by
      simp only [Header.natWord, List.length_append, List.length_replicate, List.length_cons]
      omega
    simp only [List.length_reverse, wordLength] at normalLength
    simp only [run, joined, List.length_append, List.length_cons, List.length_nil,
      List.length_tail, prefixLength]
    omega

end PDROC.BitVM.Log.Capture
