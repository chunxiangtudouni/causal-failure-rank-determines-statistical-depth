module

public import Common.PSTR_WordVM_BlankBank_020
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Card
public import Init.Data.BitVec.Lemmas

/-! LSB-first Word meaning for the ACTUAL proved bank source. This adds
no executable address/width/control field. Current raw/ISA producers must
establish the data invariant; the address bound below is a proof variable
for original actual accesses, never a new input/performance oracle. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.WordBank

open Turing UniqueStore UniqueStore.KeyCompare UniqueStore.RecordSegments UniqueStore.BankSegments

variable {width : Nat}

def bits (word : BitVec width) : List Bool :=
  List.ofFn (fun point : Fin width => word.getLsbD point.val)

def rawValue (word : List Bool) : Nat := (BitVec.ofBoolListLE word).toNat

def readWord (width : Nat) (word : List Bool) : BitVec width := BitVec.ofNat width (rawValue word)

theorem bits_length (word : BitVec width) : (bits word).length = width := List.length_ofFn

theorem bits_injective : Function.Injective (bits : BitVec width → List Bool) := by
  intro left right same
  have functions := List.ofFn_injective same
  apply BitVec.eq_of_getLsbD_eq
  intro point within
  exact congrFun functions ⟨point, within⟩

theorem bits_getD (word : BitVec width) (point : Nat) :
    (bits word).getD point false = word.getLsbD point := by
  by_cases within : point < width
  · simp [bits, List.getD_eq_getElem?_getD, within]
  · simp [bits, List.getD_eq_getElem?_getD, within,
      BitVec.getLsbD_of_ge word point (Nat.le_of_not_gt within)]

theorem rawValue_bits (word : BitVec width) : rawValue (bits word) = word.toNat := by
  apply Nat.eq_of_testBit_eq
  intro point
  simp only [rawValue, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, bits_getD]

theorem readWord_bits (word : BitVec width) : readWord width (bits word) = word := by
  apply BitVec.eq_of_toNat_eq
  rw [readWord, BitVec.toNat_ofNat, rawValue_bits, Nat.mod_eq_of_lt word.isLt]

theorem rawValue_zero (width : Nat) : rawValue (List.replicate width false) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro point
  rw [rawValue, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, Nat.zero_testBit,
    List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem readWord_zero (width : Nat) : readWord width (List.replicate width false) = 0 := by
  rw [readWord, rawValue_zero]
  rfl

theorem rawValue_inj (left right : List Bool) (lengths : left.length = right.length)
    (same : rawValue left = rawValue right) : left = right := by
  apply List.ext_getElem lengths
  intro point leftBound rightBound
  have equalBit := congrArg (fun number : Nat => number.testBit point) same
  simpa only [rawValue, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem leftBound,
    List.getElem?_eq_getElem rightBound, Option.getD_some] using equalBit

/-- This is the interpreted heap of the concrete unique-record bank.
Absent fields decode the actual zero word emitted by UniqueRead. -/
def heap (width : Nat) (records : List Record) (address : BitVec width) : BitVec width :=
  readWord width ((records.lookup (bits address)).getD (List.replicate width false))

theorem heap_nil (width : Nat) : heap width [] = fun _ => 0 := by
  funext address
  simp only [heap, List.lookup_nil, Option.getD_none, readWord_zero]

theorem heap_upsert (address value : BitVec width) (records : List Record) :
    heap width (upsert (bits address) (bits value) records) = Function.update (heap width records) address value := by
  funext wanted
  change readWord width (((upsert (bits address) (bits value) records).lookup (bits wanted)).getD
    (List.replicate width false)) = _
  rw [WholeUpsert.lookup_upsert]
  by_cases same : wanted = address
  · subst wanted
    simp only [ite_true, Option.getD_some, readWord_bits, Function.update_self]
  · have different : bits wanted ≠ bits address := fun equal => same (bits_injective equal)
    simp only [different, ite_false, Function.update_of_ne same]
    rfl

theorem lookup_word (address : BitVec width) (records : List Record) :
    readWord width (UniqueRead.Lookup.valueOf (bits address) records) = heap width records address := by
  simp only [UniqueRead.Lookup.valueOf, bits_length, heap]

/-- Tie the actual old bank source, the exact path/count and the original
Word store function update. This does not perform the caller's old-register
copy or claim that the full instruction decoder has been constructed. -/
theorem actual_store (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (address value : BitVec width) (records : List Record)
    (sized : WholeUpsert.Sized (bits address) records) :
    PhaseRun caller (WholeUpsert.trace background flags saved e (bits address) (bits value) records [])
      (WholeUpsert.start background flags saved e (bits address) (bits value) records [])
      (WholeUpsert.finish background flags e (bits address) (bits value) records [])
      (WholeUpsert.steps (bits address) (bits value) records []) ∧
    heap width (upsert (bits address) (bits value) records) = Function.update (heap width records) address value :=
  ⟨WholeUpsert.run caller background flags saved e (bits address) (bits value) records []
      (by simp only [bits_length]) sized, heap_upsert address value records⟩

theorem actual_read (caller : Statement) (background : Stack → List Bool) (flags : CallerFlags)
    (saved : FieldCopy.Store) (e : Bool) (address : BitVec width) (oldOutput : List Bool) (records : List Record)
    (sized : WholeUpsert.Sized (bits address) records) :
    UniqueRead.Run caller (UniqueRead.Lookup.actualTrace background flags saved e (bits address) oldOutput records [])
      (UniqueRead.Lookup.entry background flags saved e (bits address) oldOutput records [])
      (UniqueRead.Lookup.finish background flags e (bits address) records [])
      (oldOutput.length + 1 + UniqueRead.Lookup.steps (bits address) records []) ∧
    readWord width ((UniqueRead.Lookup.finish background flags e (bits address) records []).stk 3) =
      heap width records address := by
  refine ⟨UniqueRead.Lookup.actual_run caller background flags saved e (bits address) oldOutput records [] sized, ?_⟩
  rw [(UniqueRead.Lookup.endpoint background flags e (bits address) records).2.1]
  exact lookup_word address records

/-- Domain bounds are internal ghost facts obtained from the SAME original
Word access. They are not executable fuel, a size parameter or extra raw I/O. -/
def Within (limit : Nat) (records : List Record) : Prop :=
  ∀ record ∈ records, rawValue record.1 < limit

theorem lookup_outside (address : BitVec width) (records : List Record) (limit : Nat)
    (within : Within limit records) (outside : limit ≤ address.toNat) :
    records.lookup (bits address) = none := by
  induction records with
  | nil => rfl
  | cons record later ih =>
    rcases record with ⟨key, word⟩
    have different : bits address ≠ key := by
      intro same
      have bound := within (key, word) (by simp)
      change rawValue key < limit at bound
      rw [← same, rawValue_bits] at bound
      omega
    have verdict : (bits address == key) = false := beq_eq_false_iff_ne.mpr different
    have tailWithin : Within limit later := by
      intro item present
      exact within item (List.mem_cons_of_mem _ present)
    simpa only [List.lookup_cons, verdict] using ih tailWithin

theorem heap_outside (address : BitVec width) (records : List Record) (limit : Nat)
    (within : Within limit records) (outside : limit ≤ address.toNat) : heap width records address = 0 := by
  rw [heap, lookup_outside address records limit within outside, Option.getD_none, readWord_zero]

theorem within_upsert (address value : BitVec width) (records : List Record) (limit : Nat)
    (inside : address.toNat < limit) (within : Within limit records) :
    Within limit (upsert (bits address) (bits value) records) := by
  intro record present
  have keyPresent : record.1 ∈ (upsert (bits address) (bits value) records).map Prod.fst :=
    List.mem_map.mpr ⟨record, present, rfl⟩
  rcases WholeUpsert.key_mem_upsert record.1 (bits address) (bits value) records keyPresent with same | previous
  · rw [same, rawValue_bits]
    exact inside
  · obtain ⟨oldRecord, oldPresent, sameKey⟩ := List.mem_map.mp previous
    rw [← sameKey]
    exact within oldRecord oldPresent

theorem records_le_allocated (query : List Bool) (records : List Record) (limit : Nat)
    (sized : WholeUpsert.Sized query records) (unique : (records.map Prod.fst).Nodup)
    (within : Within limit records) : records.length ≤ limit := by
  let keys := records.map Prod.fst
  have uniqueNat : (keys.map rawValue).Nodup := by
    apply List.Nodup.map_on ?_ unique
    intro left leftPresent right rightPresent same
    obtain ⟨leftRecord, leftMember, leftKey⟩ := List.mem_map.mp leftPresent
    obtain ⟨rightRecord, rightMember, rightKey⟩ := List.mem_map.mp rightPresent
    have leftWidth := (sized leftRecord leftMember).1
    have rightWidth := (sized rightRecord rightMember).1
    have lengths : left.length = right.length := by
      rw [← leftKey, ← rightKey]
      exact leftWidth.trans rightWidth.symm
    exact rawValue_inj left right lengths same
  have subset : (keys.map rawValue).toFinset ⊆ Finset.range limit := by
    intro address present
    obtain ⟨key, keyMember, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
    obtain ⟨record, recordMember, rfl⟩ := List.mem_map.mp keyMember
    exact Finset.mem_range.mpr (within record recordMember)
  have count := Finset.card_le_card subset
  rw [List.toFinset_card_of_nodup uniqueNat, Finset.card_range] at count
  simpa only [keys, List.length_map] using count

/-- The live bank bound is from unique actually-addressed records, not
from the number of writes or the execution clock. This lemma does not
invent an original access bound: the ISA prefix consumer must derive it. -/
theorem encoded_allocated_bound (query : List Bool) (records : List Record) (limit : Nat)
    (sized : WholeUpsert.Sized query records) (unique : (records.map Prod.fst).Nodup)
    (within : Within limit records) :
    (encodeRecords records).length ≤ (2 * query.length + 1) * limit + 1 := by
  rw [WholeUpsert.encodeRecords_length query records sized]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (records_le_allocated query records limit sized unique within)) 1

end PaperProofs.Common.Native.PSTRWordVM.WordBank
