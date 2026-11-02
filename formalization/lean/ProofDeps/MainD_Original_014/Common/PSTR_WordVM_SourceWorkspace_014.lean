module

public import Common.PSTR_WordVM_BankSegments_011

/-! Physical occupied bits of the actual fixed-bank paths. These are
TM2 macro boundaries, not an assertion about native TM1/TM0 clocks.
The transfer phases conserve occupied bits; no time bound is used as
workspace. Fin16, the roles and the executable store remain fixed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueStore.Workspace

open Turing KeyCompare BankSegments

def occupied (configuration : State) : Nat :=
  (configuration.stk 0).length + (configuration.stk 1).length +
  (configuration.stk 2).length + (configuration.stk 3).length +
  (configuration.stk 4).length + (configuration.stk 5).length +
  (configuration.stk 6).length + (configuration.stk 7).length +
  (configuration.stk 8).length + (configuration.stk 9).length +
  (configuration.stk 10).length + (configuration.stk 11).length +
  (configuration.stk 12).length + (configuration.stk 13).length +
  (configuration.stk 14).length + (configuration.stk 15).length

def outside (background : Stack → List Bool) : Nat :=
  (background 1).length + (background 4).length + (background 6).length +
  (background 8).length + (background 9).length + (background 13).length +
  (background 14).length + (background 15).length

def fieldMass (fields : Fields) : Nat :=
  fields.bank.length + fields.front.length + fields.query.length + fields.value.length +
  fields.width.length + fields.keySaved.length + fields.valueSaved.length + fields.used.length

theorem occupied_state (background : Stack → List Bool) (point : Label)
    (memory : Store) (fields : Fields) :
    occupied (state background point memory fields) = outside background + fieldMass fields := by
  unfold occupied state bankSlots outside fieldMass
  dsimp
  omega

theorem each_stack_le (configuration : State) (point : Stack) :
    (configuration.stk point).length ≤ occupied configuration := by
  fin_cases point
  · change (configuration.stk 0).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 1).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 2).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 3).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 4).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 5).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 6).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 7).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 8).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 9).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 10).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 11).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 12).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 13).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 14).length ≤ occupied configuration
    unfold occupied
    omega
  · change (configuration.stk 15).length ≤ occupied configuration
    unfold occupied
    omega

theorem compare_mass (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (key query tail : List Bool) (fields : Fields)
    (lengths : key.length = query.length) :
    ∀ current ∈ compareTrace background flags saved e key query tail fields,
      occupied current = occupied (compareStart background saved e flags key query tail fields) := by
  induction query generalizing saved e key fields with
  | nil =>
    intro current present
    simp only [compareTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  | cons queryBit rest ih =>
    cases key with
    | nil => simp at lengths
    | cons bankBit later =>
      have smaller : later.length = rest.length := by
        simp only [List.length_cons] at lengths
        omega
      intro current present
      rcases List.mem_cons.mp present with same | after
      · subst current
        rfl
      · simp only [List.head?_cons, Option.getD_some, List.tail_cons] at after
        have conserved := ih (true, queryBit) (e && (bankBit == queryBit)) later
          { fields with front := bankBit :: fields.front, keySaved := queryBit :: fields.keySaved, used := true :: fields.used }
          smaller current after
        simp only [compareStart, occupied_state, fieldMass, List.length_cons,
          List.length_append, List.length_replicate] at conserved ⊢
        omega

theorem restore_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (reversed : List Bool) (fields : Fields) :
    ∀ current ∈ restoreTrace background e flags saved reversed fields,
      occupied current = occupied (restoreStart background saved e flags reversed fields) := by
  induction reversed generalizing saved fields with
  | nil =>
    intro current present
    simp only [restoreTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  | cons queryBit rest ih =>
    intro current present
    rcases List.mem_cons.mp present with same | after
    · subst current
      rfl
    · have conserved := ih (true, queryBit)
        { fields with query := queryBit :: fields.query, width := true :: fields.width } current after
      simp only [restoreStart, occupied_state, fieldMass, List.length_cons,
        List.length_replicate] at conserved ⊢
      omega

theorem skip_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (oldValue tail : List Bool) (fields : Fields) :
    ∀ current ∈ skipTrace background e flags saved oldValue tail fields,
      occupied current = occupied (skipStart background saved e flags oldValue tail fields) := by
  induction oldValue generalizing saved fields with
  | nil =>
    intro current present
    simp only [skipTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  | cons oldBit later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | after
    · subst current
      rfl
    · have conserved := ih (true, oldBit)
        { fields with front := oldBit :: fields.front, used := true :: fields.used } current after
      simp only [skipStart, occupied_state, fieldMass, List.length_cons,
        List.length_append, List.length_replicate] at conserved ⊢
      omega

theorem width_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (amount : Nat) (fields : Fields) :
    ∀ current ∈ widthTrace background e flags saved amount fields,
      occupied current = occupied (widthStart background saved e flags amount fields) := by
  induction amount generalizing saved fields with
  | zero =>
    intro current present
    simp only [widthTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  | succ amount ih =>
    intro current present
    rcases List.mem_cons.mp present with same | after
    · subst current
      rfl
    · have conserved := ih (true, saved.2) { fields with width := true :: fields.width } current after
      simp only [widthStart, occupied_state, fieldMass, List.length_cons,
        List.length_replicate] at conserved ⊢
      omega

theorem write_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (oldValue newValue tail : List Bool) (fields : Fields)
    (lengths : oldValue.length = newValue.length) :
    ∀ current ∈ writeTrace background e flags saved oldValue newValue tail fields,
      occupied current = occupied (writeStart background saved e flags oldValue newValue tail fields) := by
  induction newValue generalizing saved oldValue fields with
  | nil =>
    intro current present
    simp only [writeTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  | cons newBit later ih =>
    cases oldValue with
    | nil => simp at lengths
    | cons oldBit restOld =>
      have smaller : restOld.length = later.length := by
        simp only [List.length_cons] at lengths
        omega
      intro current present
      rcases List.mem_cons.mp present with same | after
      · subst current
        rfl
      · simp only [List.tail_cons] at after
        have conserved := ih (true, newBit) restOld
          { fields with front := newBit :: fields.front, valueSaved := newBit :: fields.valueSaved, used := true :: fields.used }
          smaller current after
        simp only [writeStart, occupied_state, fieldMass, List.length_cons,
          List.length_append, List.length_replicate] at conserved ⊢
        omega

theorem value_back_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (reversed : List Bool) (fields : Fields) :
    ∀ current ∈ valueBackTrace background e flags saved reversed fields,
      occupied current = occupied (valueBackStart background saved e flags reversed fields) := by
  induction reversed generalizing saved fields with
  | nil =>
    intro current present
    simp only [valueBackTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  | cons newBit later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | after
    · subst current
      rfl
    · have conserved := ih (true, newBit)
        { fields with value := newBit :: fields.value, width := true :: fields.width } current after
      simp only [valueBackStart, occupied_state, fieldMass, List.length_cons,
        List.length_replicate] at conserved ⊢
      omega

theorem front_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (frontPart : List Bool) (fields : Fields) :
    ∀ current ∈ frontTrace background e flags saved frontPart fields,
      occupied current = occupied (frontStart background saved e flags frontPart fields) := by
  induction frontPart generalizing saved fields with
  | nil =>
    intro current present
    simp only [frontTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  | cons oldBit later ih =>
    intro current present
    rcases List.mem_cons.mp present with same | after
    · subst current
      rfl
    · have conserved := ih (true, oldBit) { fields with bank := oldBit :: fields.bank } current after
      simp only [frontStart, occupied_state, fieldMass, List.length_cons] at conserved ⊢
      omega

theorem front_return_mass (background : Stack → List Bool) (e : Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (frontPart : List Bool) (fields : Fields) :
    ∀ current ∈ frontReturnTrace background e flags saved frontPart fields,
      occupied current = occupied (frontStart background saved e flags frontPart fields) := by
  intro current present
  rcases List.mem_append.mp present with before | after
  · exact front_mass background e flags saved frontPart fields current before
  · have same := List.mem_singleton.mp after
    subst current
    change occupied (frontRestored background e flags frontPart fields) = _
    simp only [frontRestored, frontStart, occupied_state, fieldMass, List.length_nil,
      List.length_append, List.length_reverse]
    omega

end PaperProofs.Common.Native.PSTRWordVM.UniqueStore.Workspace
