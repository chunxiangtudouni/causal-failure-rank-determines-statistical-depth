module

public import Paid.PDROC_BitVM_Log_BankMount_050

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.BankMount

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! Complete real field-loop builder. Induction is on the specification of
the remaining encoded Cell data, bounded by6/13 via FieldData.size. It is
not a TM store list, host parse, runtime fuel or whole-run success oracle. -/

def fieldEntry (core : Bool) (cursor : ℕ) : Label :=
  if inside : cursor < fieldCount core then
    fieldLabel ⟨cursor, by have bound := fieldCount_le core; omega⟩ BankFieldRoot.startLabel
  else footerLabel

theorem nextField_entry (core : Bool) (cursor : Fin 13) :
    nextField core cursor = fieldEntry core (cursor.val + 1) := rfl

private theorem joined_last {α : Type} (left right : List α) (middle final : α)
    (leftLast : left.getLast? = some middle) (rightHead : right.head? = some middle)
    (rightLast : right.getLast? = some final) :
    (left ++ right.tail).getLast? = some final := by
  by_cases one : right.length = 1
  · obtain ⟨single, singleton⟩ := List.length_eq_one_iff.mp one
    have headEqual : single = middle := Option.some.inj (by simpa only [singleton, List.head?_cons] using rightHead)
    have lastEqual : single = final := Option.some.inj (by simpa only [singleton, List.getLast?_singleton] using rightLast)
    have equal : middle = final := headEqual.symm.trans lastEqual
    simpa only [singleton, List.tail_cons, List.tail_nil, List.append_nil, equal] using leftLast
  · simp only [List.getLast?_append, List.getLast?_tail, one, ↓reduceIte, rightLast, Option.some_or]

theorem fields_runs (core : Bool) (basis : Stack → List Bool) (processed remaining : List Cell)
    (suffix : List Bool) (contents : Stack → List Bool) (store : Store)
    (ready : FieldData core basis processed remaining suffix contents) :
    ∃ (run : List SourceState) (vars : Store) (data : Stack → List Bool),
      run.head? = some (⟨some (fieldEntry core processed.length), (store, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) ∧
      run.getLast? = some (⟨some footerLabel, (vars, ()), data⟩ : SourceState) ∧
      vars.1 = store.1 ∧ vars.2.1.2 = store.2.1.2 ∧
      FieldData core basis (processed ++ remaining) [] suffix data ∧
      run.length ≤ 2 * (remaining.flatMap encodeCellBits).length + 11 * remaining.length + 1 := by
  induction remaining generalizing processed contents store with
  | nil =>
    have count : processed.length = fieldCount core := by simpa only [List.length_nil, Nat.add_zero] using ready.size
    let before : SourceState := ⟨some footerLabel, (store, ()), contents⟩
    refine ⟨[before], store, contents, ?_, List.isChain_singleton _, rfl, rfl, rfl, ?_, ?_⟩
    · simp only [List.head?_cons, fieldEntry, count, lt_self_iff_false, ↓reduceDIte]
      rfl
    · simpa only [List.append_nil] using ready
    · simp only [List.length_cons, List.length_nil, List.flatMap_nil, Nat.mul_zero, Nat.zero_add]
      omega
  | cons value remaining ih =>
    have size := ready.size
    have limit := fieldCount_le core
    simp only [List.length_cons] at size
    have beforeBound : processed.length < fieldCount core := by omega
    have cursorBound : processed.length < 13 := by omega
    let cursor : Fin 13 := ⟨processed.length, cursorBound⟩
    let tailBytes := remaining.flatMap encodeCellBits ++ true :: suffix
    have input : contents 0 = encodeCellBits value ++ tailBytes := by
      simpa only [List.flatMap_cons, List.append_assoc] using ready.input
    obtain ⟨left, leftHead, leftChain, leftLast, leftLength⟩ :=
      field_return core cursor value tailBytes contents store input ready.ticks ready.capture
    obtain ⟨advanceBound, advanced⟩ := ready.advance value
    have advancedExact : FieldData core basis (processed ++ [value]) remaining suffix
        (BankField.result cursor value tailBytes contents) := advanced
    obtain ⟨right, vars, data, rightHead, rightChain, rightLast, savedNat, savedExtra, finalData, rightLength⟩ :=
      ih (processed ++ [value]) (BankField.result cursor value tailBytes contents) (BankFieldRoot.finished store) advancedExact
    let middle : SourceState := ⟨some (nextField core cursor), (BankFieldRoot.finished store, ()),
      BankField.result cursor value tailBytes contents⟩
    have rightHeadExact : right.head? = some middle := by
      simpa only [middle, nextField_entry, cursor, List.length_append, List.length_cons, List.length_nil] using rightHead
    let run := left ++ right.tail
    have head : run.head? = some (⟨some (fieldEntry core processed.length), (store, ()), contents⟩ : SourceState) := by
      simp only [run, List.head?_append, leftHead, Option.some_or, fieldEntry, beforeBound, ↓reduceDIte, cursor]
    have chain : run.IsChain (fun a b => TM2.step (sourceProgram core) a = some b) :=
      TwoStack.join_chain left right middle leftChain rightChain leftLast rightHeadExact
    have last : run.getLast? = some (⟨some footerLabel, (vars, ()), data⟩ : SourceState) :=
      joined_last left right middle _ leftLast rightHeadExact rightLast
    refine ⟨run, vars, data, head, chain, last, savedNat, savedExtra, ?_, ?_⟩
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using finalData
    · have tailBound : right.length - 1 ≤ 2 * (remaining.flatMap encodeCellBits).length + 11 * remaining.length := by omega
      simp only [run, List.length_append, List.length_tail, List.flatMap_cons,
        List.length_append, List.length_cons]
      omega

end PDROC.BitVM.Log.BankMount
