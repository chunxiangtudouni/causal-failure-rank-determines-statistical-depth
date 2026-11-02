module

public import Paid.PDROC_BitVM_Log_HeapRelease_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2300000

@[expose] public section

namespace PDROC.BitVM.Log.HeapRelease

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

def released (value : ℕ) (contents : Stack → List Bool) :=
  Function.update (cleaned contents) 21 (false :: (encodeNatBits value ++ contents 21))
def naturalResult (store : Store) := prependResult (pointerResult (cleared store))
def rationalResult (store : Store) := HeapPointer.setTyped (HeapPointer.saveTag (cleared store) (some true)) false

theorem marshalled_archive (value : ℕ) (contents : Stack → List Bool) : marshalled value contents 25 = [] := by
  simp [marshalled, (cleaned_work contents).2.1]

theorem marshalled_address (value : ℕ) (contents : Stack → List Bool) :
    marshalled value contents 26 = encodeNatBits value := by
  simp [marshalled, (cleaned_work contents).2.2]

theorem release_commit (value : ℕ) (contents : Stack → List Bool) :
    HeapPrepend.recordContents false (marshalled value contents) = released value contents := by
  funext index
  fin_cases index <;> simp [HeapPrepend.recordContents, marshalled, released, cleaned, cleared25, cleared24]

/-- Genuine release for a Nat pointer: actual clears, actual register read,
actual type branch and actual record prepend, then the real final HALT. -/
theorem source_natural_runs (pointer : Register) (value : ℕ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value)) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram pointer) after = none ∧
      after.l = none ∧ after.var = (naturalResult store, ()) ∧ after.stk = released value contents ∧
      run.length ≤ clearBudget contents + 30 * ((encodeNatBits value).length + 1) := by
  obtain ⟨readyTrace, readyHead, readyChain, readyLast, readyLength⟩ := natural_ready pointer value contents store register
  let actualStore := pointerResult (cleared store)
  let actualContents := marshalled value contents
  obtain ⟨bodyTrace, bodyHead, bodyChain, bodyLast, bodyLength⟩ :=
    prepend_return pointer actualContents actualStore (marshalled_archive value contents)
  let beforeBranch : SourceState := ⟨some branchLabel, (actualStore, ()), actualContents⟩
  let frontBody := beforeBranch :: bodyTrace
  have frontBodyHead : frontBody.head? = some beforeBranch := rfl
  have frontBodyChain : frontBody.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) := by
    apply List.IsChain.cons bodyChain
    intro next member
    rw [bodyHead] at member
    have equal := Option.mem_some_iff.mp member
    subst next
    exact branch_nat pointer (actualStore, ()) actualContents rfl
  have frontBodyLast : frontBody.getLast? = some (⟨some doneLabel, (naturalResult store, ()),
      HeapPrepend.recordContents false actualContents⟩ : SourceState) := by
    simp only [frontBody, List.getLast?_cons, bodyLast, Option.getD_some]
    rfl
  have bodyPositive : 0 < bodyTrace.length := by
    cases bodyTrace with
    | nil => simp only [List.head?_nil, reduceCtorEq] at bodyHead
    | cons first rest => simp only [List.length_cons]; omega
  let joined := readyTrace ++ frontBody.tail
  have joinedHead : joined.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [joined, List.head?_append, readyHead, Option.some_or]
  have joinedChain : joined.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) :=
    TwoStack.join_chain readyTrace frontBody beforeBranch readyChain frontBodyChain readyLast frontBodyHead
  have frontNotOne : frontBody.length ≠ 1 := by simp only [frontBody, List.length_cons]; omega
  have joinedLast : joined.getLast? = some (⟨some doneLabel, (naturalResult store, ()),
      released value contents⟩ : SourceState) := by
    simp only [joined, List.getLast?_append, List.getLast?_tail, frontNotOne, ↓reduceIte,
      frontBodyLast, Option.some_or]
    rw [release_commit]
  let final : SourceState := ⟨none, (naturalResult store, ()), released value contents⟩
  let run := joined ++ [final]
  have actual : run.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) := by
    apply joinedChain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [joinedLast, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    exact done_halt pointer (naturalResult store, ()) (released value contents)
  refine ⟨run, final, ?_, actual, List.getLast?_append_cons joined final [], rfl, rfl, rfl, rfl, ?_⟩
  · change (joined ++ [final]).head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState)
    simp only [List.head?_append, joinedHead, Option.some_or]
  · have bound : bodyTrace.length ≤ 20 * ((encodeNatBits value).length + 1) := by
      simpa only [actualContents, marshalled_address] using bodyLength
    simp only [run, joined, frontBody, List.length_append, List.length_cons, List.length_nil, List.length_tail]
    omega

/-- A Rat pointer really takes invalid/HALT after the true clear prefix.
All RAM register/heap/output/readonly bytes carry exactly; no tombstone writes. -/
theorem source_rational_runs (pointer : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram pointer) after = none ∧
      after.l = none ∧ after.var = (rationalResult store, ()) ∧ after.stk = cleaned contents ∧
      run.length ≤ clearBudget contents + 5 := by
  obtain ⟨readyTrace, readyHead, readyChain, readyLast, readyLength⟩ := rational_ready pointer value contents store register
  let beforeBranch : SourceState := ⟨some branchLabel, (rationalResult store, ()), cleaned contents⟩
  let invalid : SourceState := ⟨some invalidLabel, (rationalResult store, ()), cleaned contents⟩
  let final : SourceState := ⟨none, (rationalResult store, ()), cleaned contents⟩
  let tailTrace := [beforeBranch, invalid, final]
  have tailHead : tailTrace.head? = some beforeBranch := rfl
  have tailChain : tailTrace.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) := by
    apply List.isChain_cons_cons.mpr
    refine ⟨branch_invalid pointer (rationalResult store, ()) (cleaned contents) rfl, ?_⟩
    exact List.isChain_cons_cons.mpr ⟨invalid_halt pointer (rationalResult store, ()) (cleaned contents), List.isChain_singleton _⟩
  let run := readyTrace ++ tailTrace.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, readyHead, Option.some_or]
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) :=
    TwoStack.join_chain readyTrace tailTrace beforeBranch readyChain tailChain readyLast tailHead
  have last : run.getLast? = some final := by
    simp only [run, tailTrace, List.tail_cons, List.getLast?_append, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.some_or]
  refine ⟨run, final, head, chain, last, rfl, rfl, rfl, rfl, ?_⟩
  simp only [run, tailTrace, List.tail_cons, List.length_append, List.length_cons, List.length_nil]
  omega

theorem natural_runs (pointer : Register) (value : ℕ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value)) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program pointer) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer) after = none ∧
      after.l = none ∧ after.var = naturalResult store ∧ after.stk = released value contents ∧
      run.length ≤ clearBudget contents + 30 * ((encodeNatBits value).length + 1) := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := source_natural_runs pointer value contents store register
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso (sourceProgram pointer) source
      (⟨some startLabel, (store, ()), contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved, sourceVar]; rfl
  · rw [length]; exact sourceLength

theorem rational_runs (pointer : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ (run : List State) (after : State),
      run.head? = some (⟨some startLabel, store, contents⟩ : State) ∧
      run.IsChain (fun a b => TM2.step (program pointer) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer) after = none ∧
      after.l = none ∧ after.var = rationalResult store ∧ after.stk = cleaned contents ∧
      run.length ≤ clearBudget contents + 5 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := source_rational_runs pointer value contents store register
  obtain ⟨run, after, head, chain, last, halt, label, saved, data, length⟩ :=
    StoreIso.actual_trace storeIso (sourceProgram pointer) source
      (⟨some startLabel, (store, ()), contents⟩ : SourceState) sourceFinal sourceHead sourceChain sourceLast sourceHalt
  refine ⟨run, after, head, chain, last, halt, label.trans sourceDone, ?_, data.trans sourceData, ?_⟩
  · rw [saved, sourceVar]; rfl
  · rw [length]; exact sourceLength

end PDROC.BitVM.Log.HeapRelease
