module

public import Common.PSTR_WordVM_ReadValue_018

/-! ONE actual fixed finite bank read. A real clear prefix destroys only
the previous standalone output3; first-key search reads actual bits and
EOF generates zeros. Bank10 is restored, with no appended read history.
Address/Word interpretation and standard raw initialization are separate. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueRead.Lookup

open Turing UniqueStore UniqueStore.KeyCompare UniqueStore.BankSegments UniqueStore.RecordSegments

def valueOf (query : List Bool) (records : List Record) : List Bool :=
  (records.lookup query).getD (List.replicate query.length false)

def start (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query : List Bool) (records : List Record) (frontPart : List Bool) : State :=
  state background 0 (saved, (e, flags)) (workFields query [] (encodeRecords records) frontPart)

def finish (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (query : List Bool) (records : List Record) (frontPart : List Bool) : State :=
  state background 13 ((false, false), (WholeUpsert.endEqual e query records, flags))
    (workFields query (valueOf query records) (frontPart.reverse ++ encodeRecords records) [])

def trace (background : Stack → List Bool) (flags : CallerFlags) :
    FieldCopy.Store → Bool → List Bool → List Record → List Bool → List State
  | saved, e, query, [], frontPart =>
      start background flags saved e query [] frontPart :: zeroTrace background e flags (true, false) query frontPart
  | saved, e, query, (key, word) :: later, frontPart =>
      let keys := RecordSegments.keyTrace background flags (true, true) key query []
        (word ++ encodeRecords later) (true :: frontPart)
      if key = query then
        start background flags saved e query ((key, word) :: later) frontPart ::
          (keys ++ (UniqueRead.hitTrace background flags query word (encodeRecords later)
            (key.reverse ++ true :: frontPart)).tail)
      else
        start background flags saved e query ((key, word) :: later) frontPart ::
          (keys ++ (missTrace background flags query [] word (encodeRecords later)
            (key.reverse ++ true :: frontPart)).tail ++
            (trace background flags (false, FieldCopy.lastRead (false, false) word) false query later
              (word.reverse ++ key.reverse ++ true :: frontPart)).tail)

def steps (query : List Bool) : List Record → List Bool → Nat
  | [], frontPart => 2 * query.length + frontPart.length + 5
  | (key, word) :: later, frontPart =>
      if key = query then (2 * query.length + 2) +
        (2 * word.length + (key.reverse ++ true :: frontPart).length + 4) + 1
      else (2 * query.length + 2) + (2 * word.length + 2) +
        steps query later (word.reverse ++ key.reverse ++ true :: frontPart) + 1

theorem run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (query : List Bool) (records : List Record)
    (frontPart : List Bool) (sized : WholeUpsert.Sized query records) :
    Run caller (trace background flags saved e query records frontPart)
      (start background flags saved e query records frontPart)
      (finish background flags e query records frontPart) (steps query records frontPart) := by
  induction records generalizing saved e frontPart with
  | nil =>
    have after := zero_run caller background e flags query frontPart
    have sameAfter : Run caller (zeroTrace background e flags (true, false) query frontPart)
        (zeroStart background (true, false) e flags query frontPart)
        (finish background flags e query [] frontPart) (2 * query.length + frontPart.length + 4) := by
      simpa [finish, zeroEnd, valueOf, WholeUpsert.endEqual, encodeRecords] using after
    have edge : TM2.step (UniqueRead.program caller) (start background flags saved e query [] frontPart) =
        some (zeroStart background (true, false) e flags query frontPart) := by
      simpa [start, zeroStart, fillStart, encodeRecords, workFields] using
        UniqueRead.tag_eof caller background saved e flags (workFields query [] [false] frontPart) []
    simpa only [trace, steps] using Run.prepend edge sameAfter
  | cons record later ih =>
    rcases record with ⟨key, word⟩
    have headWidth : key.length = query.length ∧ word.length = query.length := sized (key, word) (by simp)
    have tailSized : WholeUpsert.Sized query later := by
      intro item present
      exact sized item (List.mem_cons_of_mem _ present)
    have keys := UniqueRead.key_run caller background flags (true, true) key query []
      (word ++ encodeRecords later) (true :: frontPart) headWidth.1
    have edge : TM2.step (UniqueRead.program caller)
        (start background flags saved e query ((key, word) :: later) frontPart) =
        some (RecordSegments.keyStart background flags (true, true) key query []
          (word ++ encodeRecords later) (true :: frontPart)) := by
      simpa [start, RecordSegments.keyStart, compareStart, encodeRecords, workFields] using
        UniqueRead.tag_true caller background saved e flags (workFields query [] (encodeRecords later) frontPart)
          (key ++ word ++ encodeRecords later)
    by_cases matched : key = query
    · have reflexiveVerdict : eqBits query query = true := (eqBits_eq_true_iff query query).mpr rfl
      have after := UniqueRead.hit_run caller background flags query word (encodeRecords later)
        (key.reverse ++ true :: frontPart) headWidth.2
      have sameAfter : Run caller
          (UniqueRead.hitTrace background flags query word (encodeRecords later) (key.reverse ++ true :: frontPart))
          (keyEnd background flags key query [] (word ++ encodeRecords later) (true :: frontPart))
          (finish background flags e query ((key, word) :: later) frontPart)
          (2 * word.length + (key.reverse ++ true :: frontPart).length + 4) := by
        simpa [key_end_fields, UniqueRead.hitStart, UniqueRead.hitEnd, finish, valueOf,
          WholeUpsert.endEqual, List.lookup_cons, Bool.beq_eq_decide_eq, matched, reflexiveVerdict,
          encodeRecords, List.reverse_append, List.reverse_cons, List.append_assoc] using after
      have actual := Run.prepend edge (keys.join sameAfter)
      simpa only [trace, steps, matched, ite_true] using actual
    · have verdict := WholeUpsert.eqBits_of_ne key query matched
      have skipped := UniqueRead.miss_run caller background flags query [] word (encodeRecords later)
        (key.reverse ++ true :: frontPart)
      have sameSkipped : Run caller
          (missTrace background flags query [] word (encodeRecords later) (key.reverse ++ true :: frontPart))
          (keyEnd background flags key query [] (word ++ encodeRecords later) (true :: frontPart))
          (missEnd background flags query [] word (encodeRecords later) (key.reverse ++ true :: frontPart))
          (2 * word.length + 2) := by
        simpa [key_end_fields, miss_start_fields, verdict, headWidth.2] using skipped
      have rest := ih (false, FieldCopy.lastRead (false, false) word) false
        (word.reverse ++ key.reverse ++ true :: frontPart) tailSized
      have sameRest : Run caller
          (trace background flags (false, FieldCopy.lastRead (false, false) word) false query later
            (word.reverse ++ key.reverse ++ true :: frontPart))
          (missEnd background flags query [] word (encodeRecords later) (key.reverse ++ true :: frontPart))
          (finish background flags e query ((key, word) :: later) frontPart)
          (steps query later (word.reverse ++ key.reverse ++ true :: frontPart)) := by
        simpa [start, miss_end_fields, finish, valueOf, List.lookup_cons, Bool.beq_eq_decide_eq,
          WholeUpsert.endEqual, encodeRecords, matched, Ne.symm matched, headWidth.2,
          List.reverse_append, List.reverse_cons, List.append_assoc] using rest
      have actual := Run.prepend edge ((keys.join sameSkipped).join sameRest)
      simpa only [trace, steps, matched, ite_false, List.append_assoc] using actual

theorem valueOf_length (query : List Bool) (records : List Record)
    (sized : WholeUpsert.Sized query records) : (valueOf query records).length = query.length := by
  induction records with
  | nil => simp [valueOf]
  | cons record later ih =>
    rcases record with ⟨key, word⟩
    have headWidth : key.length = query.length ∧ word.length = query.length := sized (key, word) (by simp)
    have tailSized : WholeUpsert.Sized query later := by
      intro item present
      exact sized item (List.mem_cons_of_mem _ present)
    by_cases matched : key = query
    · simpa [valueOf, List.lookup_cons, Bool.beq_eq_decide_eq, matched] using headWidth.2
    · simpa [valueOf, List.lookup_cons, Bool.beq_eq_decide_eq, Ne.symm matched] using ih tailSized

theorem steps_le (query : List Bool) (records : List Record) (frontPart : List Bool)
    (sized : WholeUpsert.Sized query records) :
    steps query records frontPart ≤ 8 * ((encodeRecords records).length + query.length + 1) + frontPart.length := by
  induction records generalizing frontPart with
  | nil => simp only [steps, encodeRecords, List.length_cons, List.length_nil]; omega
  | cons record later ih =>
    rcases record with ⟨key, word⟩
    have headWidth : key.length = query.length ∧ word.length = query.length := sized (key, word) (by simp)
    have tailSized : WholeUpsert.Sized query later := by
      intro item present
      exact sized item (List.mem_cons_of_mem _ present)
    have rest := ih (word.reverse ++ key.reverse ++ true :: frontPart) tailSized
    by_cases matched : key = query <;>
      simp only [steps, matched, ite_true, ite_false, encodeRecords, List.length_cons,
        List.length_append, List.length_reverse] at rest ⊢ <;> omega

theorem trace_mass (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query : List Bool) (records : List Record) (frontPart : List Bool)
    (sized : WholeUpsert.Sized query records) :
    ∀ current ∈ trace background flags saved e query records frontPart,
      Workspace.occupied current ≤ Workspace.outside background + (encodeRecords records).length +
        frontPart.length + 3 * query.length := by
  induction records generalizing saved e frontPart with
  | nil =>
    intro current present
    rcases List.mem_cons.mp present with same | filling
    · subst current
      simp only [start, Workspace.work_mass, encodeRecords, List.length_cons, List.length_nil]
      omega
    · have bound := zero_mass background e flags query frontPart current filling
      simp only [encodeRecords, List.length_cons, List.length_nil]
      omega
  | cons record later ih =>
    rcases record with ⟨key, word⟩
    have headWidth : key.length = query.length ∧ word.length = query.length := sized (key, word) (by simp)
    have tailSized : WholeUpsert.Sized query later := by
      intro item present
      exact sized item (List.mem_cons_of_mem _ present)
    intro current present
    by_cases matched : key = query
    · simp only [trace, matched, ite_true, List.mem_cons, List.mem_append] at present
      rcases present with same | comparing | copying
      · subst current
        simp only [start, Workspace.work_mass, encodeRecords, List.length_cons, List.length_append, List.length_nil]
        omega
      · have conserved := Workspace.key_mass background flags (true, true) query query []
          (word ++ encodeRecords later) (true :: frontPart) rfl current comparing
        simp only [RecordSegments.keyStart, compareStart, workFields, Workspace.occupied_state, Workspace.fieldMass,
          encodeRecords, List.length_cons, List.length_append, List.length_replicate, List.length_nil]
          at conserved ⊢
        omega
      · have bound := UniqueRead.hit_mass background flags query word (encodeRecords later)
          (query.reverse ++ true :: frontPart) headWidth.2 current (List.mem_of_mem_tail copying)
        simp only [encodeRecords, List.length_cons, List.length_append, List.length_reverse] at bound ⊢
        omega
    · simp only [trace, matched, ite_false, List.mem_cons, List.mem_append] at present
      rcases present with same | ((comparing | skipping) | continuing)
      · subst current
        simp only [start, Workspace.work_mass, encodeRecords, List.length_cons, List.length_append, List.length_nil]
        omega
      · have conserved := Workspace.key_mass background flags (true, true) key query []
          (word ++ encodeRecords later) (true :: frontPart) headWidth.1 current comparing
        simp only [RecordSegments.keyStart, compareStart, workFields, Workspace.occupied_state, Workspace.fieldMass,
          encodeRecords, List.length_cons, List.length_append, List.length_replicate, List.length_nil]
          at conserved ⊢
        omega
      · have conserved := Workspace.miss_mass background flags query [] word (encodeRecords later)
          (key.reverse ++ true :: frontPart) current (List.mem_of_mem_tail skipping)
        simp only [missStart, skipStart, workFields, Workspace.occupied_state, Workspace.fieldMass, encodeRecords,
          List.length_reverse, List.length_cons, List.length_append, List.length_replicate, List.length_nil]
          at conserved ⊢
        omega
      · have bound := ih (false, FieldCopy.lastRead (false, false) word) false
          (word.reverse ++ key.reverse ++ true :: frontPart) tailSized current (List.mem_of_mem_tail continuing)
        simp only [encodeRecords, List.length_append, List.length_cons, List.length_reverse] at bound ⊢
        omega

def entry (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store) (e : Bool)
    (query oldOutput : List Bool) (records : List Record) (frontPart : List Bool) : State :=
  clearStart background saved e flags oldOutput (workFields query oldOutput (encodeRecords records) frontPart)

def actualTrace (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store) (e : Bool)
    (query oldOutput : List Bool) (records : List Record) (frontPart : List Bool) : List State :=
  clearTrace background e flags saved oldOutput (workFields query oldOutput (encodeRecords records) frontPart) ++
    (trace background flags (false, false) e query records frontPart).tail

theorem actual_run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (query oldOutput : List Bool) (records : List Record)
    (frontPart : List Bool) (sized : WholeUpsert.Sized query records) :
    Run caller (actualTrace background flags saved e query oldOutput records frontPart)
      (entry background flags saved e query oldOutput records frontPart)
      (finish background flags e query records frontPart) (oldOutput.length + 1 + steps query records frontPart) := by
  have clearing := clear_run caller background e flags saved oldOutput
    (workFields query oldOutput (encodeRecords records) frontPart)
  have searching := run caller background flags (false, false) e query records frontPart sized
  have sameSearch : Run caller (trace background flags (false, false) e query records frontPart)
      (clearEnd background e flags (workFields query oldOutput (encodeRecords records) frontPart))
      (finish background flags e query records frontPart) (steps query records frontPart) := by
    simpa [clearEnd, start, workFields] using searching
  exact clearing.join sameSearch

theorem actual_mass (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query oldOutput : List Bool) (records : List Record) (frontPart : List Bool)
    (sized : WholeUpsert.Sized query records) :
    ∀ current ∈ actualTrace background flags saved e query oldOutput records frontPart,
      Workspace.occupied current ≤ Workspace.outside background + (encodeRecords records).length +
        frontPart.length + 3 * query.length + oldOutput.length := by
  intro current present
  rcases List.mem_append.mp present with clearing | searching
  · have bound := clear_mass background e flags saved oldOutput
      (workFields query oldOutput (encodeRecords records) frontPart) current clearing
    simp only [clearStart, workFields, Workspace.occupied_state, Workspace.fieldMass,
      List.length_replicate, List.length_nil] at bound
    omega
  · have bound := trace_mass background flags (false, false) e query records frontPart sized
      current (List.mem_of_mem_tail searching)
    omega

/-- The real bank is unchanged and the output is mature first-key lookup,
with actual all-FALSE word data for absent. This is an internal bit-bank
ABI, not yet an address interpreter or an original raw-input theorem. -/
theorem endpoint (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (query : List Bool) (records : List Record) :
    (finish background flags e query records []).stk 10 = encodeRecords records ∧
    (finish background flags e query records []).stk 3 = valueOf query records ∧
    (finish background flags e query records []).stk 2 = query ∧
    (finish background flags e query records []).stk 11 = List.replicate query.length true ∧
    (finish background flags e query records []).stk 0 = [] ∧
    (finish background flags e query records []).stk 5 = [] ∧
    (finish background flags e query records []).stk 7 = [] ∧
    (finish background flags e query records []).stk 12 = [] ∧
    (finish background flags e query records []).var.2.2 = flags := by
  simp [finish, state, workFields, at_bank, at_value, at_query, at_width, at_front,
    at_keySaved, at_valueSaved, at_used]

theorem endpoint_background (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (query : List Bool) (records : List Record) (point : Stack)
    (outside : point ≠ 0 ∧ point ≠ 2 ∧ point ≠ 3 ∧ point ≠ 5 ∧ point ≠ 7 ∧
      point ≠ 10 ∧ point ≠ 11 ∧ point ≠ 12) :
    (finish background flags e query records []).stk point = background point := by
  rcases outside with ⟨h0, h2, h3, h5, h7, h10, h11, h12⟩
  simp only [finish, state, bankSlots, h0, h2, h3, h5, h7, h10, h11, h12, ite_false]

theorem endpoint_word_length (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (query : List Bool) (records : List Record) (sized : WholeUpsert.Sized query records) :
    ((finish background flags e query records []).stk 3).length = query.length :=
  valueOf_length query records sized

end PaperProofs.Common.Native.PSTRWordVM.UniqueRead.Lookup
