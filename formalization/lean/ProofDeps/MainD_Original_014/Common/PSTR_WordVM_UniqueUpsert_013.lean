module

public import Common.PSTR_WordVM_RecordSegments_012

/-! ONE concrete path of the fixed bank source performs recursive first-key
upsert. Pure equality only DESCRIBES the path: the actual branch is proved
from KeyCompare.eqBits and real stack reads. Width/U never enters control.
Numeric allocation/physical native compilation are separate consumers. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueStore.WholeUpsert

open Turing KeyCompare BankSegments RecordSegments

def Sized (query : List Bool) (records : List Record) : Prop :=
  ∀ record ∈ records, record.1.length = query.length ∧ record.2.length = query.length

def endEqual (e : Bool) (query : List Bool) : List Record → Bool
  | [] => e
  | (key, _) :: later => if key = query then true else endEqual false query later

def start (background : Stack → List Bool) (flags : CallerFlags) (saved : FieldCopy.Store)
    (e : Bool) (query value : List Bool) (records : List Record) (frontPart : List Bool) : State :=
  state background 0 (saved, (e, flags)) (workFields query value (encodeRecords records) frontPart)

def finish (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (query value : List Bool) (records : List Record) (frontPart : List Bool) : State :=
  state background 13 ((false, false), (endEqual e query records, flags))
    (workFields query value (frontPart.reverse ++ encodeRecords (upsert query value records)) [])

def trace (background : Stack → List Bool) (flags : CallerFlags) :
    FieldCopy.Store → Bool → List Bool → List Bool → List Record → List Bool → List State
  | saved, e, query, value, [], frontPart =>
      start background flags saved e query value [] frontPart ::
        insertTrace background flags e (true, false) query value frontPart
  | saved, e, query, value, (key, oldValue) :: later, frontPart =>
      let keys := RecordSegments.keyTrace background flags (true, true) key query value
        (oldValue ++ encodeRecords later) (true :: frontPart)
      if key = query then
        start background flags saved e query value ((key, oldValue) :: later) frontPart ::
          (keys ++ (hitTrace background flags query oldValue value (encodeRecords later)
            (key.reverse ++ true :: frontPart)).tail)
      else
        start background flags saved e query value ((key, oldValue) :: later) frontPart ::
          (keys ++ (missTrace background flags query value oldValue (encodeRecords later)
            (key.reverse ++ true :: frontPart)).tail ++
            (trace background flags (false, FieldCopy.lastRead (false, false) oldValue) false query value later
              (oldValue.reverse ++ key.reverse ++ true :: frontPart)).tail)

def steps (query value : List Bool) : List Record → List Bool → Nat
  | [], frontPart => 4 * query.length + frontPart.length + 8
  | (key, oldValue) :: later, frontPart =>
      if key = query then
        (2 * query.length + 2) + (3 * value.length + (key.reverse ++ true :: frontPart).length + 4) + 1
      else
        (2 * query.length + 2) + (2 * oldValue.length + 2) +
          steps query value later (oldValue.reverse ++ key.reverse ++ true :: frontPart) + 1

theorem eqBits_of_ne (key query : List Bool) (different : key ≠ query) : eqBits key query = false := by
  cases verdict : eqBits key query with
  | false => rfl
  | true => exact (different ((eqBits_eq_true_iff key query).mp verdict)).elim

theorem run (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (query value : List Bool) (records : List Record)
    (frontPart : List Bool) (valueWidth : value.length = query.length) (sized : Sized query records) :
    PhaseRun caller (trace background flags saved e query value records frontPart)
      (start background flags saved e query value records frontPart)
      (finish background flags e query value records frontPart) (steps query value records frontPart) := by
  induction records generalizing saved e frontPart with
  | nil =>
    have after := insert_run caller background flags e (true, false) query value frontPart valueWidth
    have sameAfter : PhaseRun caller (insertTrace background flags e (true, false) query value frontPart)
        (insertStart background flags e (true, false) query value frontPart)
        (finish background flags e query value [] frontPart) (4 * query.length + frontPart.length + 7) := by
      simpa [finish, endEqual, upsert, encodeRecords, insert_end_fields] using after
    have edge : TM2.step (program caller) (start background flags saved e query value [] frontPart) =
        some (insertStart background flags e (true, false) query value frontPart) := by
      simpa [start, insertStart, encodeRecords, workFields] using
        tag_eof caller background saved e flags (workFields query value [false] frontPart) []
    simpa only [trace, steps] using PhaseRun.prepend edge sameAfter
  | cons record later ih =>
    rcases record with ⟨key, oldValue⟩
    have headWidth : key.length = query.length ∧ oldValue.length = query.length :=
      sized (key, oldValue) (by simp)
    have tailSized : Sized query later := by
      intro record present
      exact sized record (List.mem_cons_of_mem _ present)
    have keys := key_run caller background flags (true, true) key query value
      (oldValue ++ encodeRecords later) (true :: frontPart) headWidth.1
    have edge : TM2.step (program caller)
        (start background flags saved e query value ((key, oldValue) :: later) frontPart) =
        some (RecordSegments.keyStart background flags (true, true) key query value
          (oldValue ++ encodeRecords later) (true :: frontPart)) := by
      simpa [start, RecordSegments.keyStart, compareStart, encodeRecords, workFields] using
        tag_true caller background saved e flags
          (workFields query value (encodeRecords later) frontPart) (key ++ oldValue ++ encodeRecords later)
    by_cases matched : key = query
    · have reflexiveVerdict : eqBits query query = true := (eqBits_eq_true_iff query query).mpr rfl
      have after := hit_run caller background flags query oldValue value (encodeRecords later)
        (key.reverse ++ true :: frontPart) (headWidth.2.trans valueWidth.symm)
      have sameAfter : PhaseRun caller
          (hitTrace background flags query oldValue value (encodeRecords later) (key.reverse ++ true :: frontPart))
          (keyEnd background flags key query value (oldValue ++ encodeRecords later) (true :: frontPart))
          (finish background flags e query value ((key, oldValue) :: later) frontPart)
          (3 * value.length + (key.reverse ++ true :: frontPart).length + 4) := by
        simpa [key_end_fields, hit_start_fields, hit_end_fields, finish, endEqual, upsert,
          encodeRecords, matched, reflexiveVerdict, valueWidth, List.reverse_append, List.reverse_cons,
          List.append_assoc] using after
      have full := PhaseRun.prepend edge (keys.join sameAfter)
      simpa only [trace, steps, matched, ite_true] using full
    · have verdict : eqBits key query = false := eqBits_of_ne key query matched
      have skipped := miss_run caller background flags query value oldValue (encodeRecords later)
        (key.reverse ++ true :: frontPart)
      have sameSkipped : PhaseRun caller
          (missTrace background flags query value oldValue (encodeRecords later) (key.reverse ++ true :: frontPart))
          (keyEnd background flags key query value (oldValue ++ encodeRecords later) (true :: frontPart))
          (missEnd background flags query value oldValue (encodeRecords later) (key.reverse ++ true :: frontPart))
          (2 * oldValue.length + 2) := by
        simpa [key_end_fields, miss_start_fields, verdict, headWidth.2] using skipped
      have rest := ih (false, FieldCopy.lastRead (false, false) oldValue) false
        (oldValue.reverse ++ key.reverse ++ true :: frontPart) tailSized
      have sameRest : PhaseRun caller
          (trace background flags (false, FieldCopy.lastRead (false, false) oldValue) false query value later
            (oldValue.reverse ++ key.reverse ++ true :: frontPart))
          (missEnd background flags query value oldValue (encodeRecords later) (key.reverse ++ true :: frontPart))
          (finish background flags e query value ((key, oldValue) :: later) frontPart)
          (steps query value later (oldValue.reverse ++ key.reverse ++ true :: frontPart)) := by
        simpa [start, miss_end_fields, finish, endEqual, upsert, encodeRecords, matched, headWidth.2,
          List.reverse_append, List.reverse_cons, List.append_assoc] using rest
      have full := PhaseRun.prepend edge ((keys.join sameSkipped).join sameRest)
      simpa only [trace, steps, matched, ite_false, List.append_assoc] using full

/-- Original caller flags and all registers/scratches are the SAME endpoint;
the complete bank contains exactly first-key upsert, not a write history. -/
theorem endpoint_bank (background : Stack → List Bool) (flags : CallerFlags) (e : Bool)
    (query value : List Bool) (records : List Record) :
    (finish background flags e query value records []).stk 10 = encodeRecords (upsert query value records) ∧
    (finish background flags e query value records []).stk 2 = query ∧
    (finish background flags e query value records []).stk 3 = value ∧
    (finish background flags e query value records []).stk 11 = List.replicate query.length true ∧
    (finish background flags e query value records []).stk 0 = [] ∧
    (finish background flags e query value records []).stk 5 = [] ∧
    (finish background flags e query value records []).stk 7 = [] ∧
    (finish background flags e query value records []).stk 12 = [] ∧
    (finish background flags e query value records []).var.2.2 = flags := by
  simp [finish, state, workFields, at_bank, at_query, at_value, at_width, at_front,
    at_keySaved, at_valueSaved, at_used]

theorem steps_le (query value : List Bool) (records : List Record) (frontPart : List Bool)
    (valueWidth : value.length = query.length) (sized : Sized query records) :
    steps query value records frontPart ≤ 8 * ((encodeRecords records).length + query.length + 1) + frontPart.length := by
  induction records generalizing frontPart with
  | nil => simp only [steps, encodeRecords, List.length_cons, List.length_nil]; omega
  | cons record later ih =>
    rcases record with ⟨key, oldValue⟩
    have headWidth : key.length = query.length ∧ oldValue.length = query.length :=
      sized (key, oldValue) (by simp)
    have tailSized : Sized query later := by
      intro record present
      exact sized record (List.mem_cons_of_mem _ present)
    have rest := ih (oldValue.reverse ++ key.reverse ++ true :: frontPart) tailSized
    by_cases matched : key = query
    · simp only [steps, matched, ite_true, encodeRecords, List.length_cons, List.length_append,
        List.length_reverse]
      omega
    · simp only [steps, matched, ite_false, encodeRecords, List.length_cons, List.length_append,
        List.length_reverse] at rest ⊢
      omega

theorem key_mem_upsert (wanted query value : List Bool) (records : List Record)
    (present : wanted ∈ (upsert query value records).map Prod.fst) :
    wanted = query ∨ wanted ∈ records.map Prod.fst := by
  induction records with
  | nil =>
    have same : wanted = query := by simpa [upsert] using present
    exact Or.inl same
  | cons record later ih =>
    rcases record with ⟨key, oldValue⟩
    by_cases matched : key = query
    · exact Or.inr (by simpa only [upsert, matched, ite_true, List.map_cons] using present)
    · simp only [upsert, matched, ite_false, List.map_cons, List.mem_cons] at present
      rcases present with same | after
      · exact Or.inr (List.mem_cons.mpr (Or.inl same))
      · rcases ih after with same | before
        · exact Or.inl same
        · exact Or.inr (List.mem_cons_of_mem _ before)

theorem keys_nodup_upsert (query value : List Bool) (records : List Record)
    (unique : (records.map Prod.fst).Nodup) :
    ((upsert query value records).map Prod.fst).Nodup := by
  induction records with
  | nil => simp [upsert]
  | cons record later ih =>
    rcases record with ⟨key, oldValue⟩
    have split : key ∉ later.map Prod.fst ∧ (later.map Prod.fst).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using unique
    by_cases matched : key = query
    · simpa only [upsert, matched, ite_true, List.map_cons] using unique
    · simp only [upsert, matched, ite_false, List.map_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_, ih split.2⟩
      intro present
      rcases key_mem_upsert key query value later present with same | before
      · exact matched same
      · exact split.1 before

theorem sized_upsert (query value : List Bool) (records : List Record)
    (valueWidth : value.length = query.length) (sized : Sized query records) :
    Sized query (upsert query value records) := by
  induction records with
  | nil =>
    intro record present
    have same : record = (query, value) := by simpa only [upsert, List.mem_singleton] using present
    subst record
    exact ⟨rfl, valueWidth⟩
  | cons record later ih =>
    rcases record with ⟨key, oldValue⟩
    have headWidth : key.length = query.length ∧ oldValue.length = query.length :=
      sized (key, oldValue) (by simp)
    have tailSized : Sized query later := by
      intro record present
      exact sized record (List.mem_cons_of_mem _ present)
    by_cases matched : key = query
    · intro record present
      simp only [upsert, matched, ite_true, List.mem_cons] at present
      rcases present with rfl | after
      · exact ⟨rfl, valueWidth⟩
      · exact tailSized record after
    · intro record present
      simp only [upsert, matched, ite_false, List.mem_cons] at present
      rcases present with rfl | after
      · exact headWidth
      · exact ih tailSized record after

/-- Use the mature first-key List.lookup; no new abstract lookup primitive
or runtime answer is added to the executable source. -/
theorem lookup_upsert (wanted query value : List Bool) (records : List Record) :
    (upsert query value records).lookup wanted =
      if wanted = query then some value else records.lookup wanted := by
  induction records with
  | nil =>
    by_cases selected : wanted = query <;> simp_all [upsert, List.lookup_cons, Bool.beq_eq_decide_eq]
  | cons record later ih =>
    rcases record with ⟨key, oldValue⟩
    by_cases matched : key = query <;> by_cases selected : wanted = key <;>
      by_cases target : wanted = query <;> simp_all [upsert, List.lookup_cons, Bool.beq_eq_decide_eq]

theorem upsert_length_le (query value : List Bool) (records : List Record) :
    (upsert query value records).length ≤ records.length + 1 := by
  induction records with
  | nil => exact Nat.le_refl 1
  | cons record later ih =>
    rcases record with ⟨key, oldValue⟩
    by_cases matched : key = query <;> simp only [upsert, matched, ite_true, ite_false, List.length_cons] <;> omega

/-- Canonical field widths make the storage bound linear in the actual
number of unique records, rather than the number of writes. -/
theorem encodeRecords_length (query : List Bool) (records : List Record) (sized : Sized query records) :
    (encodeRecords records).length = (2 * query.length + 1) * records.length + 1 := by
  induction records with
  | nil => simp only [encodeRecords, List.length_cons, List.length_nil, Nat.mul_zero, Nat.zero_add]
  | cons record later ih =>
    rcases record with ⟨key, oldValue⟩
    have headWidth : key.length = query.length ∧ oldValue.length = query.length :=
      sized (key, oldValue) (by simp)
    have tailSized : Sized query later := by
      intro record present
      exact sized record (List.mem_cons_of_mem _ present)
    rw [show encodeRecords ((key, oldValue) :: later) = true :: (key ++ oldValue ++ encodeRecords later) from rfl]
    simp only [List.length_cons, List.length_append, ih tailSized, Nat.mul_add, Nat.mul_one]
    omega

theorem no_write_history (query value : List Bool) (records : List Record)
    (unique : (records.map Prod.fst).Nodup) (valueWidth : value.length = query.length)
    (sized : Sized query records) :
    ((upsert query value records).map Prod.fst).Nodup ∧
    Sized query (upsert query value records) ∧
    (upsert query value records).length ≤ records.length + 1 ∧
    ∀ wanted, (upsert query value records).lookup wanted =
      if wanted = query then some value else records.lookup wanted :=
  ⟨keys_nodup_upsert query value records unique, sized_upsert query value records valueWidth sized,
    upsert_length_le query value records, fun wanted => lookup_upsert wanted query value records⟩

end PaperProofs.Common.Native.PSTRWordVM.UniqueStore.WholeUpsert
