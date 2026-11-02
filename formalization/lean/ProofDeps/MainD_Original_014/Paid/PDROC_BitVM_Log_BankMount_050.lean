module

public import Paid.PDROC_BitVM_Log_BankMount_049

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

namespace PDROC.BitVM.Log.BankMount

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! Boundary data for the real field loop. This is NOT asserted at each
intermediate Cell-scan/drain state. The processed list is a specification of
already copied Bool words, never a runtime list/counter or a parse oracle. -/

def bankWords (processed : List Cell) (field : Fin 13) : List Bool :=
  ((processed[field.val]?).map encodeCellBits).getD []

theorem bankWords_nil (field : Fin 13) : bankWords [] field = [] := rfl

theorem bankWords_cursor (processed : List Cell) (bound : processed.length < 13) :
    bankWords processed ⟨processed.length, bound⟩ = [] := by
  simp only [bankWords, List.getElem?_length, Option.map_none, Option.getD_none]

theorem bankWords_append (processed : List Cell) (value : Cell) (bound : processed.length < 13) :
    bankWords (processed ++ [value]) =
      Function.update (bankWords processed) ⟨processed.length, bound⟩ (encodeCellBits value) := by
  funext field
  by_cases current : field.val = processed.length
  · have equal : field = ⟨processed.length, bound⟩ := Fin.ext current
    subst field
    rw [Function.update_self]
    simp [bankWords]
  · have different : field ≠ ⟨processed.length, bound⟩ := by
      intro equal
      exact current (congrArg Fin.val equal)
    rw [Function.update_of_ne different]
    by_cases earlier : field.val < processed.length
    · simp only [bankWords, List.getElem?_append_left earlier]
    · have oldAbsent : processed.length ≤ field.val := by omega
      have newAbsent : (processed ++ [value]).length ≤ field.val := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      simp only [bankWords, List.getElem?_eq_none oldAbsent, List.getElem?_eq_none newAbsent]

theorem bankSlot_injective : Function.Injective BankDrain.bankSlot := by
  intro left right equal
  have values := congrArg Fin.val equal
  change left.val + 1 = right.val + 1 at values
  apply Fin.ext
  omega

def Outside (index : Stack) : Prop := 14 ≤ index.val ∧ index ≠ 24 ∧ index ≠ 25 ∧ index ≠ 29

theorem result_outside (field : Fin 13) (value : Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (index : Stack) (outside : Outside index) :
    BankField.result field value suffix contents index = contents index := by
  have notBank := (BankDrain.bankSlot_ne field index (Or.inr outside.1)).symm
  have not0 : index ≠ 0 := by intro equal; subst index; norm_num [Outside] at outside
  simp only [BankField.result, BankDrain.drained, BankCell.captured,
    Function.update_of_ne notBank, Function.update_of_ne outside.2.2.2,
    Function.update_of_ne outside.2.2.1, Function.update_of_ne not0]

theorem result_other_bank (field other : Fin 13) (value : Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (different : other ≠ field) :
    BankField.result field value suffix contents (BankDrain.bankSlot other) = contents (BankDrain.bankSlot other) := by
  have notBank : BankDrain.bankSlot other ≠ BankDrain.bankSlot field := fun equal => different (bankSlot_injective equal)
  have not0 := BankDrain.bankSlot_ne other 0 (by decide)
  have not25 := BankDrain.bankSlot_ne other 25 (by decide)
  have not29 := BankDrain.bankSlot_ne other 29 (by decide)
  simp only [BankField.result, BankDrain.drained, BankCell.captured,
    Function.update_of_ne notBank, Function.update_of_ne not29,
    Function.update_of_ne not25, Function.update_of_ne not0]

theorem result_work (field : Fin 13) (value : Cell) (suffix : List Bool) (contents : Stack → List Bool) :
    BankField.result field value suffix contents 24 = contents 24 ∧
      BankField.result field value suffix contents 29 = [] ∧
      BankField.result field value suffix contents 25 = (encodeCellBits value).reverse ++ contents 25 := by
  have not24 := (BankDrain.bankSlot_ne field 24 (by decide)).symm
  have not25 := (BankDrain.bankSlot_ne field 25 (by decide)).symm
  have not29 := (BankDrain.bankSlot_ne field 29 (by decide)).symm
  simp [BankField.result, BankDrain.drained, BankCell.captured, not24, not25, not29]

/-- All fields are facts at completed macro boundaries. Arbitrary caller
registers, heap, output and inactive work are retained by exact carry. -/
structure FieldData (core : Bool) (basis : Stack → List Bool) (processed remaining : List Cell)
    (suffix : List Bool) (contents : Stack → List Bool) : Prop where
  size : processed.length + remaining.length = fieldCount core
  input : contents 0 = remaining.flatMap encodeCellBits ++ true :: suffix
  ticks : contents 24 = []
  capture : contents 29 = []
  banks : ∀ field : Fin 13, contents (BankDrain.bankSlot field) = bankWords processed field
  archive : contents 25 = (encodeNatBits (fieldCount core) ++ processed.flatMap encodeCellBits).reverse
  frame : ∀ index : Stack, Outside index → contents index = basis index

theorem FieldData.advance {core : Bool} {basis contents : Stack → List Bool}
    {processed remaining : List Cell} {suffix : List Bool} (value : Cell)
    (before : FieldData core basis processed (value :: remaining) suffix contents) :
    ∃ bound : processed.length < 13,
      FieldData core basis (processed ++ [value]) remaining suffix
        (BankField.result ⟨processed.length, bound⟩ value (remaining.flatMap encodeCellBits ++ true :: suffix) contents) := by
  have countBound := fieldCount_le core
  have size := before.size
  simp only [List.length_cons] at size
  have bound : processed.length < 13 := by omega
  let cursor : Fin 13 := ⟨processed.length, bound⟩
  let tailBytes := remaining.flatMap encodeCellBits ++ true :: suffix
  refine ⟨bound, ?_⟩
  change FieldData core basis (processed ++ [value]) remaining suffix (BankField.result cursor value tailBytes contents)
  constructor
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · exact BankField.result_input cursor value tailBytes contents
  · exact (result_work cursor value tailBytes contents).1.trans before.ticks
  · exact (result_work cursor value tailBytes contents).2.1
  · intro field
    rw [bankWords_append processed value bound]
    by_cases current : field = cursor
    · subst field
      rw [Function.update_self, BankField.result_bank, before.banks, bankWords_cursor, List.append_nil]
    · rw [Function.update_of_ne current, result_other_bank cursor field value tailBytes contents current]
      exact before.banks field
  · rw [(result_work cursor value tailBytes contents).2.2, before.archive]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.reverse_append, List.append_assoc]
  · intro index outside
    exact (result_outside cursor value tailBytes contents index outside).trans (before.frame index outside)

theorem preCleared_input (contents : Stack → List Bool) : preCleared 16 contents 0 = contents 0 := by
  have absent : ¬∃ stage : Fin 16, stage.val < 16 ∧ preSlot stage = 0 := by
    rintro ⟨stage, earlier, same⟩
    fin_cases stage <;> norm_num [preSlot, BankDrain.bankSlot] at same
  simp only [preCleared, absent, ↓reduceIte]

theorem preCleared_bank (contents : Stack → List Bool) (field : Fin 13) :
    preCleared 16 contents (BankDrain.bankSlot field) = [] := by
  let stage : Fin 16 := ⟨field.val, by omega⟩
  simpa [preSlot, stage, field.isLt] using preCleared_slot contents stage

theorem preCleared_work (contents : Stack → List Bool) :
    preCleared 16 contents 24 = [] ∧ preCleared 16 contents 25 = [] ∧ preCleared 16 contents 29 = [] := by
  constructor
  · simpa [preSlot] using preCleared_slot contents 13
  · constructor
    · simpa [preSlot] using preCleared_slot contents 14
    · simpa [preSlot] using preCleared_slot contents 15

theorem preCleared_outside (contents : Stack → List Bool) (index : Stack) (outside : Outside index) :
    preCleared 16 contents index = contents index := by
  have not24 : index.val ≠ 24 := fun same => outside.2.1 (Fin.ext same)
  have not25 : index.val ≠ 25 := fun same => outside.2.2.1 (Fin.ext same)
  have not29 : index.val ≠ 29 := fun same => outside.2.2.2 (Fin.ext same)
  have lower := outside.1
  have absent : ¬∃ stage : Fin 16, stage.val < 16 ∧ preSlot stage = index := by
    rintro ⟨stage, earlier, same⟩
    have values := congrArg Fin.val same
    fin_cases stage <;> norm_num [preSlot, BankDrain.bankSlot] at values <;> omega
  simp only [preCleared, absent, ↓reduceIte]

def headerReady (core : Bool) (cells : List Cell) (suffix : List Bool) (contents : Stack → List Bool) :=
  BankHeader.result (fieldCount core) (cells.flatMap encodeCellBits ++ true :: suffix) (preCleared 16 contents)

/-- True clears and the true header result supply the initial boundary.
No whole caller supplies an initialized bank or an empty work qualification. -/
theorem FieldData.initial (core : Bool) (cells : List Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (size : cells.length = fieldCount core) :
    FieldData core contents [] cells suffix (headerReady core cells suffix contents) := by
  constructor
  · simpa only [List.length_nil, Nat.zero_add] using size
  · simp only [headerReady, BankHeader.result, Function.update_of_ne (by decide : (0 : Stack) ≠ 25), Function.update_self]
  · simp only [headerReady, BankHeader.result, Function.update_of_ne (by decide : (24 : Stack) ≠ 25),
      Function.update_of_ne (by decide : (24 : Stack) ≠ 0), (preCleared_work contents).1]
  · simp only [headerReady, BankHeader.result, Function.update_of_ne (by decide : (29 : Stack) ≠ 25),
      Function.update_of_ne (by decide : (29 : Stack) ≠ 0), (preCleared_work contents).2.2]
  · intro field
    have not0 := BankDrain.bankSlot_ne field 0 (by decide)
    have not25 := BankDrain.bankSlot_ne field 25 (by decide)
    simp only [headerReady, BankHeader.result, Function.update_of_ne not25,
      Function.update_of_ne not0, preCleared_bank, bankWords_nil]
  · simp only [headerReady, BankHeader.result, Function.update_self, (preCleared_work contents).2.1,
      List.append_nil, List.flatMap_nil]
  · intro index outside
    have not0 : index ≠ 0 := by intro equal; subst index; norm_num [Outside] at outside
    rw [headerReady, BankHeader.result, Function.update_of_ne outside.2.2.1, Function.update_of_ne not0]
    exact preCleared_outside contents index outside

end PDROC.BitVM.Log.BankMount
