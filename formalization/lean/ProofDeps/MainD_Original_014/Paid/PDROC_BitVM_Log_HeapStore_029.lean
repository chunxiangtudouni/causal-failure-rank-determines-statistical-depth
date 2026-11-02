module

public import Paid.PDROC_BitVM_Log_HeapStore_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.Log.HeapStore

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

def copied (address : ℕ) (valueSource : Register) (contents : Stack → List Bool) :=
  Function.update (marshalled address contents) 28 (contents (registerSlot valueSource))
def stored (address : ℕ) (valueSource : Register) (contents : Stack → List Bool) :=
  Function.update (Function.update (cleaned contents) 28 []) 21
    (true :: (encodeNatBits address ++ (contents (registerSlot valueSource) ++ contents 21)))
def naturalResult (store : Store) := prependResult (cleared (pointerResult (cleared store)))
def rationalResult (store : Store) := HeapPointer.setTyped (HeapPointer.saveTag (cleared store) (some true)) false

theorem marshalled_register (address : ℕ) (reg : Register) (contents : Stack → List Bool) :
    marshalled address contents (registerSlot reg) = contents (registerSlot reg) := by
  cases reg <;> simp [marshalled, cleaned, cleared25, cleared24, registerSlot,
    PaperProofs.Structure.LaminarTree.IndexedRAM.Register.word]

theorem marshalled_work (address : ℕ) (contents : Stack → List Bool) :
    marshalled address contents 24 = [] ∧ marshalled address contents 25 = [] ∧
      marshalled address contents 26 = encodeNatBits address ∧ marshalled address contents 28 = contents 28 := by
  simp [marshalled, cleaned, cleared25, cleared24]

theorem copied_fields (address : ℕ) (valueSource : Register) (contents : Stack → List Bool) :
    copied address valueSource contents 25 = [] ∧ copied address valueSource contents 26 = encodeNatBits address ∧
      copied address valueSource contents 28 = contents (registerSlot valueSource) := by
  simp [copied, marshalled, cleaned, cleared25, cleared24]

theorem store_commit (address : ℕ) (valueSource : Register) (contents : Stack → List Bool) :
    HeapPrepend.recordContents true (copied address valueSource contents) = stored address valueSource contents := by
  funext index
  fin_cases index <;> simp [HeapPrepend.recordContents, copied, stored, marshalled, cleaned, cleared25, cleared24]

/-- Actual source-register Cell bytes are copied before record construction.
The real old28 clear is paid. Pointer and source may name the SAME register. -/
theorem source_natural_runs (pointer valueSource : Register) (address : ℕ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural address)) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram pointer valueSource) after = none ∧
      after.l = none ∧ after.var = (naturalResult store, ()) ∧ after.stk = stored address valueSource contents ∧
      run.length ≤ clearBudget contents + (contents 28).length +
        50 * ((encodeNatBits address).length + (contents (registerSlot valueSource)).length + 1) := by
  obtain ⟨readyTrace, readyHead, readyChain, readyLast, readyLength⟩ :=
    natural_ready pointer valueSource address contents store register
  let pointerStore := pointerResult (cleared store)
  let pointerContents := marshalled address contents
  obtain ⟨copyTrace, copyHead, copyChain, copyLast, copyLength⟩ :=
    transfer_return pointer valueSource pointerContents pointerStore (marshalled_work address contents).1
  have copyLastExact : copyTrace.getLast? = some (⟨some (prependLabel HeapPrepend.startLabel),
      (cleared pointerStore, ()), copied address valueSource contents⟩ : SourceState) := by
    simpa only [pointerContents, marshalled_register, copied] using copyLast
  let beforeBranch : SourceState := ⟨some branchLabel, (pointerStore, ()), pointerContents⟩
  let copyFront := beforeBranch :: copyTrace
  have copyFrontHead : copyFront.head? = some beforeBranch := rfl
  have copyFrontChain : copyFront.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) := by
    apply List.IsChain.cons copyChain
    intro next member
    rw [copyHead] at member
    have equal := Option.mem_some_iff.mp member
    subst next
    exact branch_nat pointer valueSource (pointerStore, ()) pointerContents rfl
  have copyFrontLast : copyFront.getLast? = some (⟨some (prependLabel HeapPrepend.startLabel),
      (cleared pointerStore, ()), copied address valueSource contents⟩ : SourceState) := by
    simp only [copyFront, List.getLast?_cons, copyLastExact, Option.getD_some]
  let joinedCopy := readyTrace ++ copyFront.tail
  have copyPositive : 0 < copyTrace.length := by omega
  have copyFrontNotOne : copyFront.length ≠ 1 := by simp only [copyFront, List.length_cons]; omega
  have joinedCopyHead : joinedCopy.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [joinedCopy, List.head?_append, readyHead, Option.some_or]
  have joinedCopyChain : joinedCopy.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) :=
    TwoStack.join_chain readyTrace copyFront beforeBranch readyChain copyFrontChain readyLast copyFrontHead
  have joinedCopyLast : joinedCopy.getLast? = some (⟨some (prependLabel HeapPrepend.startLabel),
      (cleared pointerStore, ()), copied address valueSource contents⟩ : SourceState) := by
    simp only [joinedCopy, List.getLast?_append, List.getLast?_tail, copyFrontNotOne, ↓reduceIte,
      copyFrontLast, Option.some_or]
  obtain ⟨bodyTrace, bodyHead, bodyChain, bodyLast, bodyLength⟩ :=
    prepend_return pointer valueSource (copied address valueSource contents) (cleared pointerStore)
      (copied_fields address valueSource contents).1
  let final : SourceState := ⟨none, (naturalResult store, ()), stored address valueSource contents⟩
  let bodyFull := bodyTrace ++ [final]
  have bodyFullHead : bodyFull.head? = some (⟨some (prependLabel HeapPrepend.startLabel),
      (cleared pointerStore, ()), copied address valueSource contents⟩ : SourceState) := by
    simp only [bodyFull, List.head?_append, bodyHead, Option.some_or]
  have bodyFullChain : bodyFull.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) := by
    apply bodyChain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [bodyLast, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    rw [store_commit]
    exact done_halt pointer valueSource (naturalResult store, ()) (stored address valueSource contents)
  have bodyPositive : 0 < bodyTrace.length := by
    cases bodyTrace with
    | nil => simp only [List.head?_nil, reduceCtorEq] at bodyHead
    | cons first rest => simp only [List.length_cons]; omega
  have bodyNotOne : bodyFull.length ≠ 1 := by simp only [bodyFull, List.length_append, List.length_cons, List.length_nil]; omega
  have bodyFullLast : bodyFull.getLast? = some final := List.getLast?_append_cons bodyTrace final []
  let run := joinedCopy ++ bodyFull.tail
  have head : run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
    simp only [run, List.head?_append, joinedCopyHead, Option.some_or]
  let middle : SourceState := ⟨some (prependLabel HeapPrepend.startLabel),
    (cleared pointerStore, ()), copied address valueSource contents⟩
  have chain : run.IsChain (fun a b => TM2.step (sourceProgram pointer valueSource) a = some b) :=
    TwoStack.join_chain joinedCopy bodyFull middle joinedCopyChain bodyFullChain joinedCopyLast bodyFullHead
  have last : run.getLast? = some final := by
    simp only [run, List.getLast?_append, List.getLast?_tail, bodyNotOne, ↓reduceIte,
      bodyFullLast, Option.some_or]
  refine ⟨run, final, head, chain, last, rfl, rfl, rfl, rfl, ?_⟩
  have exactCopy : copyTrace.length = (contents 28).length + 2 * (contents (registerSlot valueSource)).length + 6 := by
    simpa only [pointerContents, marshalled_register, (marshalled_work address contents).2.2.2] using copyLength
  have boundBody : bodyTrace.length ≤ 20 * ((encodeNatBits address).length + (contents (registerSlot valueSource)).length + 1) := by
    simpa only [(copied_fields address valueSource contents).2.1, (copied_fields address valueSource contents).2.2] using bodyLength
  simp only [run, joinedCopy, copyFront, bodyFull, List.length_append, List.length_cons, List.length_nil, List.length_tail]
  omega

end PDROC.BitVM.Log.HeapStore
