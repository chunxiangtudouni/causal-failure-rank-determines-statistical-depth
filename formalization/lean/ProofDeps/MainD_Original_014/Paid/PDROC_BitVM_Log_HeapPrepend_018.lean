module

public import Paid.PDROC_BitVM_Log_HeapPrepend_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.Log.HeapPrepend

open Turing
open PDROC.BitVM.Native

/-! The full real record constructor. All updates below describe the proven
post-state of literal pop/push code; no host update appears in the program. -/

def cleared (store : SourceStore) : SourceStore := ((none, store.1.2), store.2)
def drained (phase : Phase) (contents : Stack → List Bool) : Stack → List Bool :=
  Function.update (Function.update contents (sourceSlot phase) []) (targetSlot phase)
    ((contents (sourceSlot phase)).reverse ++ contents (targetSlot phase))
def seeded (stored : Bool) (contents : Stack → List Bool) := Function.update contents 25 (stored :: contents 25)
def addressed (stored : Bool) (contents : Stack → List Bool) := drained 0 (seeded stored contents)
def prepared (stored : Bool) (contents : Stack → List Bool) :=
  if stored then drained 1 (addressed stored contents) else addressed stored contents
def completed (stored : Bool) (contents : Stack → List Bool) := drained 2 (prepared stored contents)
def payloadLength (stored : Bool) (contents : Stack → List Bool) := if stored then (contents 28).length else 0

/-- Actual seed/address/optionalCell path. The release code returns directly
from its address drain to history; no unexecuted block is given a fake step. -/
theorem prefix_runs (stored : Bool) (contents : Stack → List Bool) (store : SourceStore) :
    ∃ run : List SourceState,
      run.head? = some (sourceState (some startLabel) store contents) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram stored) a = some b) ∧
      run.getLast? = some (sourceState (some (historyLabel 0)) (cleared store) (prepared stored contents)) ∧
      run.length ≤ (contents 26).length + payloadLength stored contents + 8 := by
  obtain ⟨addressTrace, addressHead, addressChain, addressLast, addressLength⟩ :=
    phase_return_runs stored 0 (seeded stored contents) store
  let frontTrace := sourceState (some startLabel) store contents :: addressTrace
  have frontHead : frontTrace.head? = some (sourceState (some startLabel) store contents) := rfl
  have frontChain : frontTrace.IsChain (fun a b => TM2.step (sourceProgram stored) a = some b) := by
    apply List.IsChain.cons addressChain
    intro next member
    rw [addressHead] at member
    have equal := Option.mem_some_iff.mp member
    subst next
    exact seed_step stored store contents
  have frontLast : frontTrace.getLast? = some (sourceState (some (phaseReturn stored 0))
      (cleared store) (addressed stored contents)) := by
    simp only [frontTrace, List.getLast?_cons, addressLast, Option.getD_some]
    rfl
  have frontLength : frontTrace.length = (contents 26).length + 4 := by
    have exactLength : addressTrace.length = (contents 26).length + 3 := by
      simpa [sourceSlot, seeded] using addressLength
    simp only [frontTrace, List.length_cons]
    omega
  cases stored with
  | false =>
    refine ⟨frontTrace, frontHead, frontChain, frontLast, ?_⟩
    change frontTrace.length ≤ (contents 26).length + 8
    omega
  | true =>
    obtain ⟨cellTrace, cellHead, cellChain, cellLast, cellLength⟩ :=
      phase_return_runs true 1 (addressed true contents) (cleared store)
    let middle := sourceState (some (cellLabel 0)) (cleared store) (addressed true contents)
    let joined := frontTrace ++ cellTrace.tail
    have joinedHead : joined.head? = some (sourceState (some startLabel) store contents) := by
      simp only [joined, List.head?_append, frontHead, Option.some_or]
    have joinedChain : joined.IsChain (fun a b => TM2.step (sourceProgram true) a = some b) :=
      TwoStack.join_chain frontTrace cellTrace middle frontChain cellChain frontLast cellHead
    have notOne : cellTrace.length ≠ 1 := by omega
    have joinedLast : joined.getLast? = some (sourceState (some (historyLabel 0))
        (cleared store) (prepared true contents)) := by
      simp only [joined, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
        cellLast, Option.some_or]
      rfl
    refine ⟨joined, joinedHead, joinedChain, joinedLast, ?_⟩
    have cellExact : cellTrace.length = (contents 28).length + 3 := by
      simpa [addressed, drained, seeded, sourceSlot, targetSlot] using cellLength
    simp only [joined, List.length_append, List.length_tail, payloadLength, ↓reduceIte]
    omega

theorem prepared_length (stored : Bool) (contents : Stack → List Bool) :
    ((prepared stored contents) 25).length = (contents 26).length + payloadLength stored contents + (contents 25).length + 1 := by
  cases stored <;>
    simp [prepared, addressed, drained, seeded, sourceSlot, targetSlot, payloadLength, Nat.add_assoc, Nat.add_comm]

/-- ONE actual full seed/drain/HALT source path, including all EOF tests and
the actual return edges. Costs depend on physical words, not an external clock. -/
theorem source_runs (stored : Bool) (contents : Stack → List Bool) (store : SourceStore) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (sourceState (some startLabel) store contents) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram stored) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram stored) after = none ∧
      after.l = none ∧ after.var = cleared store ∧ after.stk = completed stored contents ∧
      run.length ≤ 20 * ((contents 26).length + payloadLength stored contents + (contents 25).length + 1) := by
  obtain ⟨frontTrace, frontHead, frontChain, frontLast, frontLength⟩ := prefix_runs stored contents store
  obtain ⟨historyTrace, historyHead, historyChain, historyLast, historyLength⟩ :=
    phase_return_runs stored 2 (prepared stored contents) (cleared store)
  let middle := sourceState (some (historyLabel 0)) (cleared store) (prepared stored contents)
  let joined := frontTrace ++ historyTrace.tail
  have joinedHead : joined.head? = some (sourceState (some startLabel) store contents) := by
    simp only [joined, List.head?_append, frontHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step (sourceProgram stored) a = some b) :=
    TwoStack.join_chain frontTrace historyTrace middle frontChain historyChain frontLast historyHead
  have notOne : historyTrace.length ≠ 1 := by omega
  have joinedLast : joined.getLast? = some (sourceState (some doneLabel) (cleared store) (completed stored contents)) := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
      historyLast, Option.some_or]
    rfl
  let final := sourceState none (cleared store) (completed stored contents)
  let run := joined ++ [final]
  have actual : run.IsChain (fun a b => TM2.step (sourceProgram stored) a = some b) := by
    apply joinedChain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [joinedLast, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    exact done_halt stored (cleared store) (completed stored contents)
  refine ⟨run, final, ?_, actual, List.getLast?_append_cons joined final [], rfl, rfl, rfl, rfl, ?_⟩
  · change (joined ++ [final]).head? = some (sourceState (some startLabel) store contents)
    simp only [List.head?_append, joinedHead, Option.some_or]
  · have exactHistory : historyTrace.length = ((prepared stored contents) 25).length + 3 := by
      simpa [sourceSlot] using historyLength
    rw [prepared_length] at exactHistory
    simp only [run, joined, List.length_append, List.length_cons, List.length_nil, List.length_tail]
    omega

def recordContents (stored : Bool) (contents : Stack → List Bool) : Stack → List Bool :=
  Function.update
    (Function.update (Function.update (if stored then Function.update contents 28 [] else contents) 26 []) 25 [])
    21 (stored :: (contents 26 ++ ((if stored then contents 28 else []) ++ contents 21)))

/-- With an ACTUALLY cleared archive, the post-state is exactly a canonical
record prefix followed by all old history bytes. Release never touches28. -/
theorem completed_record (stored : Bool) (contents : Stack → List Bool) (archive : contents 25 = []) :
    completed stored contents = recordContents stored contents := by
  funext index
  cases stored <;> fin_cases index <;>
    simp [completed, prepared, addressed, drained, seeded, recordContents, sourceSlot, targetSlot,
      archive, List.reverse_append, List.append_assoc]

/-- The whole selected source path is transported once to the heap family's
finite store. Address/Cell bytes are moved, not supplied by a host encoder. -/
theorem runs (stored : Bool) (contents : Stack → List Bool) (store : Store) (archive : contents 25 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program stored) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program stored) after = none ∧
      after.l = none ∧ after.var = (store.1, ((none, store.2.1.2), store.2.2)) ∧
      after.stk = recordContents stored contents ∧
      run.length ≤ 20 * ((contents 26).length + payloadLength stored contents + 1) := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := source_runs stored contents (storeIso.symm store)
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso (sourceProgram stored) source
      (sourceState (some startLabel) (storeIso.symm store) contents) sourceFinal
      sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, ?_, chain, last, halt, label.trans sourceDone, ?_, ?_, ?_⟩
  · exact head
  · rw [saved, sourceVar]
    rfl
  · exact (data.trans sourceData).trans (completed_record stored contents archive)
  · rw [length]
    simpa only [archive, List.length_nil, Nat.add_zero] using sourceLength

end PDROC.BitVM.Log.HeapPrepend
