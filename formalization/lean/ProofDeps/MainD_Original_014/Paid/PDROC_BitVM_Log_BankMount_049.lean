module

public import Paid.PDROC_BitVM_Log_BankMount_048

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

namespace PDROC.BitVM.Log.BankMount

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Native

/-! Select each genuine component path ONCE and return it into the actual
fixed mount program. Code agreement is the literal agreement in048; it is
not a successful parse, numeric result or whole-run oracle. -/

private theorem clear_return_at (core : Bool) (target : Stack) (labels : HeapClear.Label → Label) (ret : Label)
    (agrees : ∀ label, sourceProgram core (labels label) =
      Inline.statement (τ := Unit) labels ret (HeapClear.program target label))
    (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (labels 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) ∧
      run.getLast? = some (⟨some ret, (HeapLoad.cleared store, ()), Function.update contents target []⟩ : SourceState) ∧
      run.length = (contents target).length + 3 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := HeapClear.runs target contents store
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace labels ret (HeapClear.program target) (sourceProgram core) agrees source
      (⟨some 0, store, contents⟩ : HeapClear.State) sourceFinal () sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (HeapLoad.cleared store, ()) :=
    saved.trans (congrArg (fun vars : Store => (vars, ())) sourceVar)
  have finalData : after.stk = Function.update contents target [] := data.trans sourceData
  have afterEq : after = (⟨some ret, (HeapLoad.cleared store, ()), Function.update contents target []⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some ret at returned
    change vars = (HeapLoad.cleared store, ()) at finalVar
    change current = Function.update contents target [] at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, length.trans sourceLength⟩
  simpa only [afterEq] using last

theorem clear_return (core : Bool) (stage : Fin 16) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (clearLabel stage 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) ∧
      run.getLast? = some (⟨some (nextClear stage), (HeapLoad.cleared store, ()),
        Function.update contents (preSlot stage) []⟩ : SourceState) ∧
      run.length = (contents (preSlot stage)).length + 3 :=
  clear_return_at core (preSlot stage) (clearLabel stage) (nextClear stage) (clear_agrees core stage) contents store

theorem clean_return (core : Bool) (stage : Fin 3) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (cleanLabel stage 0), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) ∧
      run.getLast? = some (⟨some (nextClean stage), (HeapLoad.cleared store, ()),
        Function.update contents (cleanSlot stage) []⟩ : SourceState) ∧
      run.length = (contents (cleanSlot stage)).length + 3 :=
  clear_return_at core (cleanSlot stage) (cleanLabel stage) (nextClean stage) (clean_agrees core stage) contents store

theorem header_return (core : Bool) (count : ℕ) (suffix : List Bool)
    (contents : Stack → List Bool) (store : Store)
    (input : contents 0 = encodeNatBits count ++ suffix) (ticks : contents 24 = []) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (headerLabel BankHeader.startLabel), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) ∧
      run.getLast? = some (⟨some (fieldLabel 0 BankFieldRoot.startLabel), (BankHeader.finished store, ()),
        BankHeader.result count suffix contents⟩ : SourceState) ∧
      run.length = 2 * natBits count + 5 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := BankHeader.runs count suffix contents store input ticks
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace headerLabel (fieldLabel 0 BankFieldRoot.startLabel) BankHeader.program (sourceProgram core)
      (header_agrees core) source (⟨some BankHeader.startLabel, store, contents⟩ : BankHeader.State) sourceFinal ()
      sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (BankHeader.finished store, ()) :=
    saved.trans (congrArg (fun vars : Store => (vars, ())) sourceVar)
  have finalData : after.stk = BankHeader.result count suffix contents := data.trans sourceData
  have afterEq : after = (⟨some (fieldLabel 0 BankFieldRoot.startLabel), (BankHeader.finished store, ()),
      BankHeader.result count suffix contents⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some (fieldLabel 0 BankFieldRoot.startLabel) at returned
    change vars = (BankHeader.finished store, ()) at finalVar
    change current = BankHeader.result count suffix contents at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, length.trans sourceLength⟩
  simpa only [afterEq] using last

theorem field_return (core : Bool) (field : Fin 13) (value : Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (store : Store)
    (input : contents 0 = encodeCellBits value ++ suffix) (ticks : contents 24 = []) (capture : contents 29 = []) :
    ∃ run : List SourceState,
      run.head? = some (⟨some (fieldLabel field BankFieldRoot.startLabel), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) ∧
      run.getLast? = some (⟨some (nextField core field), (BankFieldRoot.finished store, ()),
        BankField.result field value suffix contents⟩ : SourceState) ∧
      run.length ≤ 2 * (encodeCellBits value).length + 11 := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ := BankFieldRoot.runs field value suffix contents store input ticks capture
  obtain ⟨run, after, head, chain, last, returned, data, saved, length⟩ :=
    Inline.actual_return_trace (fieldLabel field) (nextField core field) (BankFieldRoot.program field) (sourceProgram core)
      (field_agrees core field) source (⟨some BankFieldRoot.startLabel, store, contents⟩ : BankFieldRoot.State) sourceFinal ()
      sourceHead sourceChain sourceLast sourceHalt
  have finalVar : after.var = (BankFieldRoot.finished store, ()) :=
    saved.trans (congrArg (fun vars : Store => (vars, ())) sourceVar)
  have finalData : after.stk = BankField.result field value suffix contents := data.trans sourceData
  have afterEq : after = (⟨some (nextField core field), (BankFieldRoot.finished store, ()),
      BankField.result field value suffix contents⟩ : SourceState) := by
    rcases after with ⟨label, vars, current⟩
    change label = some (nextField core field) at returned
    change vars = (BankFieldRoot.finished store, ()) at finalVar
    change current = BankField.result field value suffix contents at finalData
    subst label; subst vars; subst current
    rfl
  refine ⟨run, head, chain, ?_, ?_⟩
  · simpa only [afterEq] using last
  · rw [length]; exact sourceLength

/-! Sixteen actual old-word clears. The proof index is bounded by the fixed
finite label set; no such counter or stage list is a runtime store field. -/

theorem preSlot_injective : Function.Injective preSlot := by
  intro left right equal
  fin_cases left <;> fin_cases right <;> simp_all [preSlot, BankDrain.bankSlot]

def preCleared (count : ℕ) (contents : Stack → List Bool) : Stack → List Bool :=
  fun index => if ∃ stage : Fin 16, stage.val < count ∧ preSlot stage = index then [] else contents index

def clearEntry (count : ℕ) : Label :=
  if inside : count < 16 then clearLabel ⟨count, inside⟩ 0 else headerLabel BankHeader.startLabel

def clearFlags (count : ℕ) (store : Store) := if count = 0 then store else HeapLoad.cleared store

def preCap (contents : Stack → List Bool) :=
  Finset.univ.sum (fun stage : Fin 16 => (contents (preSlot stage)).length)

def clearBudget (contents : Stack → List Bool) := 16 * (preCap contents + 3) + 1

theorem preCleared_zero (contents : Stack → List Bool) : preCleared 0 contents = contents := by
  funext index
  simp [preCleared]

theorem preCleared_current (count : ℕ) (inside : count < 16) (contents : Stack → List Bool) :
    preCleared count contents (preSlot ⟨count, inside⟩) = contents (preSlot ⟨count, inside⟩) := by
  have absent : ¬∃ stage : Fin 16, stage.val < count ∧ preSlot stage = preSlot ⟨count, inside⟩ := by
    rintro ⟨stage, earlier, same⟩
    have equal := preSlot_injective same
    have values := congrArg Fin.val equal
    change stage.val = count at values
    omega
  simp only [preCleared, absent, ↓reduceIte]

theorem preCleared_step (count : ℕ) (inside : count < 16) (contents : Stack → List Bool) :
    Function.update (preCleared count contents) (preSlot ⟨count, inside⟩) [] = preCleared (count + 1) contents := by
  funext index
  by_cases here : index = preSlot ⟨count, inside⟩
  · subst index
    rw [Function.update_self]
    have written : ∃ stage : Fin 16, stage.val < count + 1 ∧ preSlot stage = preSlot ⟨count, inside⟩ :=
      ⟨⟨count, inside⟩, by change count < count + 1; omega, rfl⟩
    simp only [preCleared, written, ↓reduceIte]
  · rw [Function.update_of_ne here]
    have predicates : (∃ stage : Fin 16, stage.val < count ∧ preSlot stage = index) ↔
        (∃ stage : Fin 16, stage.val < count + 1 ∧ preSlot stage = index) := by
      constructor
      · rintro ⟨stage, earlier, same⟩
        exact ⟨stage, by omega, same⟩
      · rintro ⟨stage, earlier, same⟩
        have different : stage.val ≠ count := by
          intro value
          have equal : stage = ⟨count, inside⟩ := Fin.ext value
          subst stage
          exact here same.symm
        exact ⟨stage, by omega, same⟩
    simp only [preCleared, predicates]

theorem preCap_bound (stage : Fin 16) (contents : Stack → List Bool) :
    (contents (preSlot stage)).length ≤ preCap contents := by
  simpa only [preCap] using
    (Finset.single_le_sum_of_canonicallyOrdered
      (f := fun index : Fin 16 => (contents (preSlot index)).length) (Finset.mem_univ stage))

theorem clearFlags_step (count : ℕ) (store : Store) :
    HeapLoad.cleared (clearFlags count store) = clearFlags (count + 1) store := by
  by_cases zero : count = 0 <;> simp [clearFlags, zero, HeapLoad.cleared]

theorem clear_prefix_runs (core : Bool) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) ∧
      run.getLast? = some (⟨some (headerLabel BankHeader.startLabel), (HeapLoad.cleared store, ()),
        preCleared 16 contents⟩ : SourceState) ∧ run.length ≤ clearBudget contents := by
  have build : ∀ count : ℕ, count ≤ 16 → ∃ run : List SourceState,
      run.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) ∧
      run.getLast? = some (⟨some (clearEntry count), (clearFlags count store, ()), preCleared count contents⟩ : SourceState) ∧
      run.length ≤ count * (preCap contents + 3) + 1 := by
    intro count
    induction count with
    | zero =>
      intro _
      let first : SourceState := ⟨some startLabel, (store, ()), contents⟩
      refine ⟨[first], rfl, List.isChain_singleton _, ?_, by simp⟩
      simp only [List.getLast?_singleton, clearEntry, clearFlags, preCleared_zero]
      rfl
    | succ count ih =>
      intro bound
      have inside : count < 16 := by omega
      obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ := ih (by omega)
      obtain ⟨right, rightHead, rightChain, rightLast, rightLength⟩ :=
        clear_return core ⟨count, inside⟩ (preCleared count contents) (clearFlags count store)
      let middle : SourceState := ⟨some (clearEntry count), (clearFlags count store, ()), preCleared count contents⟩
      have rightHeadExact : right.head? = some middle := by
        simpa only [middle, clearEntry, inside, ↓reduceDIte] using rightHead
      let joined := left ++ right.tail
      have head : joined.head? = some (⟨some startLabel, (store, ()), contents⟩ : SourceState) := by
        simp only [joined, List.head?_append, leftHead, Option.some_or]
      have chain : joined.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) :=
        TwoStack.join_chain left right middle leftChain rightChain leftLast rightHeadExact
      have notOne : right.length ≠ 1 := by omega
      have rightLastExact : right.getLast? = some (⟨some (clearEntry (count + 1)),
          (clearFlags (count + 1) store, ()), preCleared (count + 1) contents⟩ : SourceState) := by
        rw [clearFlags_step, preCleared_step] at rightLast
        exact rightLast
      have last : joined.getLast? = some (⟨some (clearEntry (count + 1)),
          (clearFlags (count + 1) store, ()), preCleared (count + 1) contents⟩ : SourceState) := by
        simp only [joined, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte, rightLastExact, Option.some_or]
      refine ⟨joined, head, chain, last, ?_⟩
      have stageLength : right.length ≤ preCap contents + 3 := by
        rw [rightLength, preCleared_current]
        exact Nat.add_le_add_right (preCap_bound ⟨count, inside⟩ contents) 3
      have tailBound : right.length - 1 ≤ preCap contents + 3 := (Nat.sub_le _ _).trans stageLength
      simp only [joined, List.length_append, List.length_tail]
      calc
        left.length + (right.length - 1) ≤ (count * (preCap contents + 3) + 1) + (preCap contents + 3) :=
          Nat.add_le_add leftLength tailBound
        _ = (count + 1) * (preCap contents + 3) + 1 := by ring
  obtain ⟨run, head, chain, last, length⟩ := build 16 (by omega)
  refine ⟨run, head, chain, ?_, length⟩
  simpa [clearEntry, clearFlags] using last

theorem preCleared_slot (contents : Stack → List Bool) (stage : Fin 16) :
    preCleared 16 contents (preSlot stage) = [] := by
  have written : ∃ previous : Fin 16, previous.val < 16 ∧ preSlot previous = preSlot stage :=
    ⟨stage, stage.isLt, rfl⟩
  simp only [preCleared, written, ↓reduceIte]

end PDROC.BitVM.Log.BankMount
