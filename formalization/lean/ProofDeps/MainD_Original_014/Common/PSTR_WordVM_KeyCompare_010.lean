module

public import Common.PSTR_WordVM_UniqueStoreCode_007

/-! Actual key comparison of the fixed UniqueStore source. Fields below
are mathematical trace descriptors, NEVER the executable finite store.
Each bit is read from the real bank/query stacks; no equality answer is
supplied to the program. A separate phase restores the query and tally. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueStore.KeyCompare

open Turing

structure Fields where
  bank : List Bool
  front : List Bool
  query : List Bool
  value : List Bool
  width : List Bool
  keySaved : List Bool
  valueSaved : List Bool
  used : List Bool

def bankSlots (background : Stack → List Bool) (fields : Fields) : Stack → List Bool :=
  fun point => if point = 0 then fields.front else if point = 2 then fields.query else
    if point = 3 then fields.value else if point = 5 then fields.keySaved else
      if point = 7 then fields.valueSaved else if point = 10 then fields.bank else
        if point = 11 then fields.width else if point = 12 then fields.used else background point

theorem at_front (background : Stack → List Bool) (fields : Fields) :
    bankSlots background fields 0 = fields.front := rfl
theorem at_query (background : Stack → List Bool) (fields : Fields) :
    bankSlots background fields 2 = fields.query := rfl
theorem at_value (background : Stack → List Bool) (fields : Fields) :
    bankSlots background fields 3 = fields.value := rfl
theorem at_keySaved (background : Stack → List Bool) (fields : Fields) :
    bankSlots background fields 5 = fields.keySaved := rfl
theorem at_valueSaved (background : Stack → List Bool) (fields : Fields) :
    bankSlots background fields 7 = fields.valueSaved := rfl
theorem at_bank (background : Stack → List Bool) (fields : Fields) :
    bankSlots background fields 10 = fields.bank := rfl
theorem at_width (background : Stack → List Bool) (fields : Fields) :
    bankSlots background fields 11 = fields.width := rfl
theorem at_used (background : Stack → List Bool) (fields : Fields) :
    bankSlots background fields 12 = fields.used := rfl

theorem update_front (background : Stack → List Bool) (fields : Fields) (value : List Bool) :
    Function.update (bankSlots background fields) 0 value = bankSlots background { fields with front := value } := by
  funext point; fin_cases point <;> rfl
theorem update_query (background : Stack → List Bool) (fields : Fields) (value : List Bool) :
    Function.update (bankSlots background fields) 2 value = bankSlots background { fields with query := value } := by
  funext point; fin_cases point <;> rfl
theorem update_value (background : Stack → List Bool) (fields : Fields) (value : List Bool) :
    Function.update (bankSlots background fields) 3 value = bankSlots background { fields with value := value } := by
  funext point; fin_cases point <;> rfl
theorem update_keySaved (background : Stack → List Bool) (fields : Fields) (value : List Bool) :
    Function.update (bankSlots background fields) 5 value = bankSlots background { fields with keySaved := value } := by
  funext point; fin_cases point <;> rfl
theorem update_valueSaved (background : Stack → List Bool) (fields : Fields) (value : List Bool) :
    Function.update (bankSlots background fields) 7 value = bankSlots background { fields with valueSaved := value } := by
  funext point; fin_cases point <;> rfl
theorem update_bank (background : Stack → List Bool) (fields : Fields) (value : List Bool) :
    Function.update (bankSlots background fields) 10 value = bankSlots background { fields with bank := value } := by
  funext point; fin_cases point <;> rfl
theorem update_width (background : Stack → List Bool) (fields : Fields) (value : List Bool) :
    Function.update (bankSlots background fields) 11 value = bankSlots background { fields with width := value } := by
  funext point; fin_cases point <;> rfl
theorem update_used (background : Stack → List Bool) (fields : Fields) (value : List Bool) :
    Function.update (bankSlots background fields) 12 value = bankSlots background { fields with used := value } := by
  funext point; fin_cases point <;> rfl

def state (background : Stack → List Bool) (point : Label) (memory : Store) (fields : Fields) : State :=
  ⟨some point, memory, bankSlots background fields⟩

theorem tag_true (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) (tail : List Bool) :
    TM2.step (program caller) (state background 0 (saved, (e, flags)) { fields with bank := true :: tail }) =
      some (state background 1 ((true, true), (true, flags))
        { fields with bank := tail, front := true :: fields.front }) := by
  simp [state, program, TM2.step, TM2.stepAux, captureData, initializeEqual, bit, jump,
    at_bank, at_front, update_bank, update_front]

theorem tag_eof (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) (tail : List Bool) :
    TM2.step (program caller) (state background 0 (saved, (e, flags)) { fields with bank := false :: tail }) =
      some (state background 7 ((true, false), (e, flags)) { fields with bank := false :: tail }) := by
  simp [state, program, TM2.step, TM2.stepAux, captureData, bit, jump, at_bank, update_bank]

theorem compare_bit (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields)
    (bankBit queryBit : Bool) (bankTail queryTail widthTail : List Bool) :
    TM2.step (program caller) (state background 1 (saved, (e, flags))
      { fields with bank := bankBit :: bankTail, query := queryBit :: queryTail, width := true :: widthTail }) =
      some (state background 1 ((true, queryBit), (e && (bankBit == queryBit), flags))
        { fields with bank := bankTail, query := queryTail, width := widthTail, front := bankBit :: fields.front, keySaved := queryBit :: fields.keySaved, used := true :: fields.used }) := by
  simp [state, program, widthBranch, TM2.step, TM2.stepAux, captureWidth, captureData,
    captureCompare, present, bit, jump, at_width, at_bank, at_front, at_query, at_keySaved,
    at_used, update_width, update_bank, update_front, update_query, update_keySaved, update_used]

theorem compare_done (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (program caller) (state background 1 (saved, (e, flags)) { fields with width := [] }) =
      some (state background 2 ((false, saved.2), (e, flags)) { fields with width := [] }) := by
  simp [state, program, widthBranch, TM2.step, TM2.stepAux, captureWidth, present, jump,
    at_width, update_width]

theorem restore_bit (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields)
    (queryBit : Bool) (queryTail usedTail : List Bool) :
    TM2.step (program caller) (state background 2 (saved, (e, flags))
      { fields with keySaved := queryBit :: queryTail, used := true :: usedTail }) =
      some (state background 2 ((true, queryBit), (e, flags))
        { fields with query := queryBit :: fields.query, width := true :: fields.width, keySaved := queryTail, used := usedTail }) := by
  simp [state, program, restoreWidth, TM2.step, TM2.stepAux, captureData, present, bit, jump,
    at_keySaved, at_query, at_used, at_width, update_keySaved, update_query, update_used, update_width]

theorem restore_done (caller : Statement) (background : Stack → List Bool)
    (saved : FieldCopy.Store) (e : Bool) (flags : CallerFlags) (fields : Fields) :
    TM2.step (program caller) (state background 2 (saved, (e, flags)) { fields with keySaved := [] }) =
      some (state background (if e then 3 else 5) ((false, false), (e, flags))
        { fields with keySaved := [] }) := by
  cases e <;> simp [state, program, TM2.step, TM2.stepAux, captureData, present, equal, jump,
    at_keySaved, update_keySaved]

def eqBits : List Bool → List Bool → Bool
  | [], [] => true
  | left :: laterLeft, right :: laterRight => (left == right) && eqBits laterLeft laterRight
  | _, _ => false

theorem eqBits_eq_true_iff (key query : List Bool) : eqBits key query = true ↔ key = query := by
  induction key generalizing query with
  | nil => cases query <;> simp [eqBits]
  | cons left later ih =>
    cases query with
    | nil => simp [eqBits]
    | cons right rest => cases left <;> cases right <;> simp_all [eqBits]

def compareStart (background : Stack → List Bool) (saved : FieldCopy.Store)
    (e : Bool) (flags : CallerFlags) (key query tail : List Bool) (fields : Fields) : State :=
  state background 1 (saved, (e, flags))
    { fields with bank := key ++ tail, query := query, width := List.replicate query.length true }

def compareStopped (background : Stack → List Bool) (saved : FieldCopy.Store)
    (e : Bool) (flags : CallerFlags) (key tail : List Bool) (fields : Fields) : State :=
  state background 2 ((false, saved.2), (e, flags))
    { fields with bank := key ++ tail, query := [], width := [] }

def compared (background : Stack → List Bool) (saved : FieldCopy.Store)
    (e : Bool) (flags : CallerFlags) (key query tail : List Bool) (fields : Fields) : State :=
  state background 2 ((false, FieldCopy.lastRead saved query), (e && eqBits key query, flags))
    { fields with bank := tail, query := [], width := [], front := key.reverse ++ fields.front, keySaved := query.reverse ++ fields.keySaved, used := List.replicate query.length true ++ fields.used }

def compareTrace (background : Stack → List Bool) (flags : CallerFlags) :
    FieldCopy.Store → Bool → List Bool → List Bool → List Bool → Fields → List State
  | saved, e, key, [], tail, fields =>
      [compareStart background saved e flags key [] tail fields,
        compareStopped background saved e flags key tail fields]
  | saved, e, key, queryBit :: rest, tail, fields =>
      compareStart background saved e flags key (queryBit :: rest) tail fields ::
        compareTrace background flags (true, queryBit) (e && (key.head?.getD false == queryBit))
          key.tail rest tail { fields with front := key.head?.getD false :: fields.front, keySaved := queryBit :: fields.keySaved, used := true :: fields.used }

theorem compareTrace_nonempty (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (key query tail : List Bool) (fields : Fields) :
    compareTrace background flags saved e key query tail fields ≠ [] := by
  cases query <;> intro equality <;> cases equality

theorem compareTrace_head (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (key query tail : List Bool) (fields : Fields) :
    (compareTrace background flags saved e key query tail fields).head? =
      some (compareStart background saved e flags key query tail fields) := by
  cases query <;> rfl

theorem compareTrace_chain (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (key query tail : List Bool) (fields : Fields)
    (lengths : key.length = query.length) :
    (compareTrace background flags saved e key query tail fields).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction query generalizing saved e key fields with
  | nil =>
    cases key with
    | nil =>
      apply List.isChain_cons_cons.mpr
      refine ⟨?_, List.isChain_singleton _⟩
      simpa only [compareStart, compareStopped, List.nil_append, List.length_nil, List.replicate_zero] using
        compare_done caller background saved e flags { fields with bank := tail, query := [] }
    | cons _ _ => simp at lengths
  | cons queryBit rest ih =>
    cases key with
    | nil => simp at lengths
    | cons bankBit later =>
      have smaller : later.length = rest.length := by
        simp only [List.length_cons] at lengths
        omega
      apply FieldCopy.prepend_chain (TM2.step (program caller)) _ _ _
        (compareTrace_head _ _ _ _ _ _ _ _)
      · simpa only [compareStart, List.cons_append, List.length_cons, List.replicate_succ,
        List.head?_cons, Option.getD_some, List.tail_cons] using
          compare_bit caller background saved e flags fields bankBit queryBit
            (later ++ tail) rest (List.replicate rest.length true)
      · exact ih _ _ _ _ smaller

theorem compareTrace_last (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (key query tail : List Bool) (fields : Fields)
    (lengths : key.length = query.length) :
    (compareTrace background flags saved e key query tail fields).getLast? =
      some (compared background saved e flags key query tail fields) := by
  induction query generalizing saved e key fields with
  | nil =>
    cases key with
    | nil => simp [compareTrace, compareStart, compareStopped, compared, eqBits, FieldCopy.lastRead]
    | cons _ _ => simp at lengths
  | cons queryBit rest ih =>
    cases key with
    | nil => simp at lengths
    | cons bankBit later =>
      have smaller : later.length = rest.length := by
        simp only [List.length_cons] at lengths
        omega
      rw [compareTrace, FieldCopy.last_cons_of_nonempty _ _ (compareTrace_nonempty _ _ _ _ _ _ _ _)]
      change (compareTrace background flags (true, queryBit) (e && (bankBit == queryBit)) later rest tail
        { fields with front := bankBit :: fields.front, keySaved := queryBit :: fields.keySaved, used := true :: fields.used }).getLast? = _
      rw [ih _ _ _ _ smaller]
      simp only [compared, eqBits, FieldCopy.lastRead, List.reverse_cons, List.length_cons,
        List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append, Bool.and_assoc]

theorem compareTrace_length (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (key query tail : List Bool) (fields : Fields) :
    (compareTrace background flags saved e key query tail fields).length = query.length + 2 := by
  induction query generalizing saved e key fields with
  | nil => rfl
  | cons queryBit rest ih => simp only [compareTrace, List.length_cons, ih]

def restoreStart (background : Stack → List Bool) (saved : FieldCopy.Store)
    (e : Bool) (flags : CallerFlags) (reversed : List Bool) (fields : Fields) : State :=
  state background 2 (saved, (e, flags))
    { fields with keySaved := reversed, used := List.replicate reversed.length true }

def restored (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (reversed : List Bool) (fields : Fields) : State :=
  state background (if e then 3 else 5) ((false, false), (e, flags))
    { fields with query := reversed.reverse ++ fields.query, width := List.replicate reversed.length true ++ fields.width, keySaved := [], used := [] }

def restoreTrace (background : Stack → List Bool) (e : Bool) (flags : CallerFlags) :
    FieldCopy.Store → List Bool → Fields → List State
  | saved, [], fields => [restoreStart background saved e flags [] fields, restored background e flags [] fields]
  | saved, queryBit :: rest, fields =>
      restoreStart background saved e flags (queryBit :: rest) fields ::
        restoreTrace background e flags (true, queryBit) rest
          { fields with query := queryBit :: fields.query, width := true :: fields.width }

theorem restoreTrace_nonempty (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (reversed : List Bool) (fields : Fields) :
    restoreTrace background e flags saved reversed fields ≠ [] := by
  cases reversed <;> intro equality <;> cases equality

theorem restoreTrace_head (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (reversed : List Bool) (fields : Fields) :
    (restoreTrace background e flags saved reversed fields).head? =
      some (restoreStart background saved e flags reversed fields) := by
  cases reversed <;> rfl

theorem restoreTrace_chain (caller : Statement) (background : Stack → List Bool)
    (e : Bool) (flags : CallerFlags) (saved : FieldCopy.Store) (reversed : List Bool) (fields : Fields) :
    (restoreTrace background e flags saved reversed fields).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction reversed generalizing saved fields with
  | nil =>
    apply List.isChain_cons_cons.mpr
    refine ⟨?_, List.isChain_singleton _⟩
    simpa only [restoreStart, restored, List.length_nil, List.replicate_zero, List.reverse_nil, List.nil_append] using
      restore_done caller background saved e flags { fields with used := [] }
  | cons queryBit rest ih =>
    apply FieldCopy.prepend_chain (TM2.step (program caller)) _ _ _ (restoreTrace_head _ _ _ _ _ _)
    · simpa only [restoreStart, List.length_cons, List.replicate_succ] using
        restore_bit caller background saved e flags fields queryBit rest (List.replicate rest.length true)
    · exact ih _ _

theorem restoreTrace_last (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (reversed : List Bool) (fields : Fields) :
    (restoreTrace background e flags saved reversed fields).getLast? =
      some (restored background e flags reversed fields) := by
  induction reversed generalizing saved fields with
  | nil => rfl
  | cons queryBit rest ih =>
    rw [restoreTrace, FieldCopy.last_cons_of_nonempty _ _ (restoreTrace_nonempty _ _ _ _ _ _), ih]
    simp only [restored, List.reverse_cons, List.length_cons, List.replicate_succ',
      List.append_assoc, List.cons_append, List.nil_append]

theorem restoreTrace_length (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (reversed : List Bool) (fields : Fields) :
    (restoreTrace background e flags saved reversed fields).length = reversed.length + 2 := by
  induction reversed generalizing saved fields with
  | nil => rfl
  | cons queryBit rest ih => simp only [restoreTrace, List.length_cons, ih]

end PaperProofs.Common.Native.PSTRWordVM.UniqueStore.KeyCompare
