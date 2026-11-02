module

public import Common.PSTR_WordVM_SourceWorkspace_014
public import Common.PSTR_WordVM_UniqueUpsert_013

/-! Occupied physical bits along ONE actual unique-bank upsert. All
boundary states are members of the very trace proved operational in013.
The eight background stacks are charged once. Search/replace conserves
mass; insertion adds at most one fixed-width record, never a write log. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueStore.Workspace

open Turing KeyCompare BankSegments RecordSegments

def valueOutside (background : Stack → List Bool) : Nat :=
  (background 0).length + (background 1).length + (background 2).length +
  (background 4).length + (background 5).length + (background 6).length +
  (background 8).length + (background 9).length + (background 13).length +
  (background 14).length + (background 15).length

def keyOutside (background : Stack → List Bool) : Nat :=
  (background 0).length + (background 1).length + (background 3).length +
  (background 4).length + (background 6).length + (background 7).length +
  (background 8).length + (background 9).length + (background 13).length +
  (background 14).length + (background 15).length

theorem value_configuration_mass (background : Stack → List Bool) (flags : TransportFlags)
    (small : FieldCopy.State) :
    occupied (FieldTransport.configuration valueRole valueLabels background flags small) =
      valueOutside background + FieldCopy.occupied small := by
  unfold occupied FieldTransport.configuration FieldTransport.slots valueRole BankCopy.role
    valueOutside FieldCopy.occupied
  dsimp
  omega

theorem key_configuration_mass (background : Stack → List Bool) (flags : TransportFlags)
    (small : FieldCopy.State) :
    occupied (FieldTransport.configuration keyRole keyLabels background flags small) =
      keyOutside background + FieldCopy.occupied small := by
  unfold occupied FieldTransport.configuration FieldTransport.slots keyRole keyOutside FieldCopy.occupied
  dsimp
  omega

theorem value_outside_work (background : Stack → List Bool) (query value bank frontPart : List Bool) :
    valueOutside (bankSlots background (workFields query value bank frontPart)) =
      outside background + frontPart.length + query.length := by
  unfold valueOutside bankSlots workFields outside
  dsimp
  omega

theorem key_outside_work (background : Stack → List Bool) (query value bank frontPart : List Bool) :
    keyOutside (bankSlots background (workFields query value bank frontPart)) =
      outside background + frontPart.length + value.length := by
  unfold keyOutside bankSlots workFields outside
  dsimp
  omega

theorem value_copy_mass (background : Stack → List Bool) (flags : TransportFlags)
    (saved : FieldCopy.Store) (word suffix target : List Bool) :
    ∀ current ∈ UniqueStore.valueTrace background flags saved word suffix target,
      occupied current ≤ valueOutside background + 3 * word.length + suffix.length + target.length := by
  intro current present
  obtain ⟨small, inside, rfl⟩ := List.mem_map.mp present
  rw [value_configuration_mass]
  have bound := FieldCopy.copyPortTrace_mass saved word suffix target small inside
  omega

theorem key_copy_mass (background : Stack → List Bool) (flags : TransportFlags)
    (saved : FieldCopy.Store) (word suffix target : List Bool) :
    ∀ current ∈ UniqueStore.keyTrace background flags saved word suffix target,
      occupied current ≤ keyOutside background + 3 * word.length + suffix.length + target.length := by
  intro current present
  obtain ⟨small, inside, rfl⟩ := List.mem_map.mp present
  rw [key_configuration_mass]
  have bound := FieldCopy.copyPortTrace_mass saved word suffix target small inside
  omega

theorem work_mass (background : Stack → List Bool) (point : Label) (memory : Store)
    (query value bank frontPart : List Bool) :
    occupied (state background point memory (workFields query value bank frontPart)) =
      outside background + bank.length + frontPart.length + 2 * query.length + value.length := by
  simp only [occupied_state, workFields, fieldMass, List.length_replicate, List.length_nil]
  omega

theorem key_mass (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (key query value tail frontPart : List Bool) (lengths : key.length = query.length) :
    ∀ current ∈ RecordSegments.keyTrace background flags saved key query value tail frontPart,
      occupied current = occupied (RecordSegments.keyStart background flags saved key query value tail frontPart) := by
  intro current present
  rcases List.mem_append.mp present with comparing | returning
  · exact compare_mass background flags saved true key query tail
      (workFields query value tail frontPart) lengths current comparing
  · have conserved := restore_mass background (eqBits key query) flags
      (false, FieldCopy.lastRead saved query) query.reverse (keyMiddle key value tail frontPart)
      current (List.mem_of_mem_tail returning)
    simp only [restoreStart, RecordSegments.keyStart, compareStart, keyMiddle, workFields,
      occupied_state, fieldMass, List.length_reverse, List.length_append, List.length_replicate,
      List.length_nil] at conserved ⊢
    omega

theorem miss_mass (background : Stack → List Bool) (flags : CallerFlags)
    (query value oldValue tail frontPart : List Bool) :
    ∀ current ∈ missTrace background flags query value oldValue tail frontPart,
      occupied current = occupied (missStart background flags query value oldValue tail frontPart) := by
  intro current present
  rcases List.mem_append.mp present with skipping | returning
  · exact skip_mass background false flags (false, false) oldValue tail
      (workFields query value tail frontPart) current skipping
  · have conserved := width_mass background false flags
      (false, FieldCopy.lastRead (false, false) oldValue) oldValue.length
      (missRestoreFields query value oldValue tail frontPart) current (List.mem_of_mem_tail returning)
    simp only [widthStart, missStart, skipStart, missRestoreFields, workFields, occupied_state,
      fieldMass, List.length_replicate, List.length_reverse, List.length_append, List.length_nil]
      at conserved ⊢
    omega

theorem hit_mass (background : Stack → List Bool) (flags : CallerFlags)
    (query oldValue newValue tail frontPart : List Bool) (lengths : oldValue.length = newValue.length) :
    ∀ current ∈ hitTrace background flags query oldValue newValue tail frontPart,
      occupied current = occupied (hitStart background flags query oldValue newValue tail frontPart) := by
  intro current present
  simp only [hitTrace, List.mem_append] at present
  rcases present with (writing | returning) | restoring
  · exact write_mass background true flags (false, false) oldValue newValue tail
      (workFields query newValue tail frontPart) lengths current writing
  · have conserved := value_back_mass background true flags
      (false, FieldCopy.lastRead (false, false) newValue) newValue.reverse
      (hitBackFields query newValue tail frontPart) current (List.mem_of_mem_tail returning)
    simp only [valueBackStart, hitBackFields, hitStart, writeStart, workFields, occupied_state,
      fieldMass, List.length_replicate, List.length_reverse, List.length_append, List.length_nil]
      at conserved ⊢
    omega
  · have conserved := front_return_mass background true flags (false, false)
      (newValue.reverse ++ frontPart) (hitFrontFields query newValue tail)
      current (List.mem_of_mem_tail restoring)
    simp only [frontStart, hitFrontFields, hitStart, writeStart, workFields, occupied_state,
      fieldMass, List.length_replicate, List.length_reverse, List.length_append, List.length_nil]
      at conserved ⊢
    omega

theorem insert_mass (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (saved : FieldCopy.Store) (query value frontPart : List Bool) (lengths : value.length = query.length) :
    ∀ current ∈ insertTrace background flags e saved query value frontPart,
      occupied current ≤ outside background + frontPart.length + 5 * query.length + 2 := by
  intro current present
  simp only [insertTrace, List.mem_append] at present
  rcases present with (copyingValue | copyingKey) | restoring
  · have bound := value_copy_mass (bankSlots background (workFields query value [false] frontPart))
      (e, flags) saved value [] [false] current copyingValue
    rw [value_outside_work] at bound
    simp only [List.length_nil, List.length_cons] at bound
    omega
  · have member := List.mem_of_mem_tail copyingKey
    rcases List.mem_append.mp member with before | tagged
    · have bound := key_copy_mass
        (bankSlots background (workFields query value (value ++ [false]) frontPart))
        (e, flags) (false, false) query [] (value ++ [false]) current before
      rw [key_outside_work] at bound
      simp only [List.length_nil, List.length_cons, List.length_append] at bound
      omega
    · have same := List.mem_singleton.mp tagged
      subst current
      rw [key_insert_tagged_fields, work_mass]
      simp only [List.length_cons, List.length_append, List.length_nil]
      omega
  · have conserved := front_return_mass background e flags (false, false) frontPart
      (insertedFields query value) current (List.mem_of_mem_tail restoring)
    simp only [frontStart, insertedFields, workFields, occupied_state, fieldMass,
      List.length_replicate, List.length_cons, List.length_append, List.length_nil] at conserved
    omega

/-- The SAME complete actual path has a peak bounded by current bank
bits plus five word fields and ONE record tag. It has no dependence on
write count or execution time; the outside physical stacks are counted. -/
theorem trace_mass (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (query value : List Bool) (records : List Record)
    (frontPart : List Bool) (valueWidth : value.length = query.length)
    (sized : WholeUpsert.Sized query records) :
    ∀ current ∈ WholeUpsert.trace background flags saved e query value records frontPart,
      occupied current ≤ outside background + (encodeRecords records).length +
        frontPart.length + 5 * query.length + 1 := by
  induction records generalizing saved e frontPart with
  | nil =>
    intro current present
    rcases List.mem_cons.mp present with same | inserting
    · subst current
      simp only [WholeUpsert.start, work_mass, encodeRecords, List.length_cons, List.length_nil]
      omega
    · have bound := insert_mass background flags e (true, false) query value frontPart valueWidth current inserting
      simp only [encodeRecords, List.length_cons, List.length_nil]
      omega
  | cons record later ih =>
    rcases record with ⟨key, oldValue⟩
    have headWidth : key.length = query.length ∧ oldValue.length = query.length :=
      sized (key, oldValue) (by simp)
    have tailSized : WholeUpsert.Sized query later := by
      intro item present
      exact sized item (List.mem_cons_of_mem _ present)
    intro current present
    by_cases matched : key = query
    · simp only [WholeUpsert.trace, matched, ite_true, List.mem_cons, List.mem_append] at present
      rcases present with same | comparing | replacing
      · subst current
        simp only [WholeUpsert.start, work_mass, encodeRecords, List.length_cons, List.length_append]
        omega
      · have conserved := key_mass background flags (true, true) query query value
          (oldValue ++ encodeRecords later) (true :: frontPart) rfl current comparing
        simp only [RecordSegments.keyStart, compareStart, workFields, occupied_state, fieldMass,
          encodeRecords, List.length_cons, List.length_append, List.length_replicate, List.length_nil]
          at conserved ⊢
        omega
      · have conserved := hit_mass background flags query oldValue value (encodeRecords later)
          (query.reverse ++ true :: frontPart) (headWidth.2.trans valueWidth.symm)
          current (List.mem_of_mem_tail replacing)
        simp only [hitStart, writeStart, workFields, occupied_state, fieldMass, encodeRecords,
          List.length_reverse, List.length_cons, List.length_append, List.length_replicate, List.length_nil]
          at conserved ⊢
        omega
    · simp only [WholeUpsert.trace, matched, ite_false, List.mem_cons, List.mem_append] at present
      rcases present with same | ((comparing | skipping) | continuing)
      · subst current
        simp only [WholeUpsert.start, work_mass, encodeRecords, List.length_cons, List.length_append]
        omega
      · have conserved := key_mass background flags (true, true) key query value
          (oldValue ++ encodeRecords later) (true :: frontPart) headWidth.1 current comparing
        simp only [RecordSegments.keyStart, compareStart, workFields, occupied_state, fieldMass,
          encodeRecords, List.length_cons, List.length_append, List.length_replicate, List.length_nil]
          at conserved ⊢
        omega
      · have conserved := miss_mass background flags query value oldValue (encodeRecords later)
          (key.reverse ++ true :: frontPart) current (List.mem_of_mem_tail skipping)
        simp only [missStart, skipStart, workFields, occupied_state, fieldMass, encodeRecords,
          List.length_reverse, List.length_cons, List.length_append, List.length_replicate, List.length_nil]
          at conserved ⊢
        omega
      · have bound := ih (false, FieldCopy.lastRead (false, false) oldValue) false
          (oldValue.reverse ++ key.reverse ++ true :: frontPart) tailSized current
          (List.mem_of_mem_tail continuing)
        simp only [encodeRecords, List.length_append, List.length_cons, List.length_reverse] at bound ⊢
        omega

theorem trace_stack_bound (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (query value : List Bool) (records : List Record)
    (frontPart : List Bool) (valueWidth : value.length = query.length)
    (sized : WholeUpsert.Sized query records) :
    ∀ current ∈ WholeUpsert.trace background flags saved e query value records frontPart,
      ∀ point, (current.stk point).length ≤ outside background + (encodeRecords records).length +
        frontPart.length + 5 * query.length + 1 := by
  intro current present point
  exact (each_stack_le current point).trans
    (trace_mass background flags saved e query value records frontPart valueWidth sized current present)

end PaperProofs.Common.Native.PSTRWordVM.UniqueStore.Workspace
