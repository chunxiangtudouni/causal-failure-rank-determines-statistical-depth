module

public import PaperProofs.Structure.IndexedNormalize
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.List.GetD
public import Init.Data.BitVec.Lemmas
public import Init.Data.Option.Lemmas
import Lean.Elab.Tactic.Omega

/-!
Actual fixed-width capacity bit streams, with an independent VOID tag.
The payload has exactly t * ceil(log_2(q+1)) Boolean cells. The scalar codec
reuses Lean's BitVec binary operations, and the vector codec concatenates
fixed-width little-endian blocks. No constant-time packed-RAM access or host
List/Vector storage/copy complexity is claimed by this storage refinement.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.CapacityBits

/-- Mathlib's exact upper base-two logarithm, including width(0)=0. -/
def width (q : Nat) : Nat := Nat.clog 2 (q + 1)

theorem width_spec (q bits : Nat) : width q ≤ bits ↔ q + 1 ≤ 2 ^ bits :=
  Nat.clog_le_iff_le_pow (by decide)

theorem value_lt_two_pow_width (q value : Nat) (hvalue : value ≤ q) : value < 2 ^ width q :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hvalue) (Nat.le_pow_clog (by decide) (q + 1))

theorem width_zero : width 0 = 0 := rfl

theorem width_eq_zero_iff (q : Nat) : width q = 0 ↔ q = 0 := by
  constructor
  · intro hzero
    have hbound := (width_spec q 0).mp (by rw [hzero])
    simp only [Nat.pow_zero] at hbound
    omega
  · rintro rfl
    exact width_zero

def encodeScalar (bits value : Nat) : List Bool :=
  List.ofFn (fun position : Fin bits => (BitVec.ofNat bits value).getLsbD position.val)

def decodeScalar (bits : List Bool) : Nat := (BitVec.ofBoolListLE bits).toNat

theorem encodeScalar_length (bits value : Nat) : (encodeScalar bits value).length = bits :=
  List.length_ofFn

theorem decodeScalar_encodeScalar (bits value : Nat) :
    decodeScalar (encodeScalar bits value) = value % 2 ^ bits := by
  let encoded := encodeScalar bits value
  have hlength : encoded.length = bits := encodeScalar_length bits value
  have hvector : (BitVec.ofBoolListLE encoded).cast hlength = BitVec.ofNat bits value := by
    apply BitVec.eq_of_getLsbD_eq
    intro position hposition
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
    have hencoded : position < encoded.length := hlength.symm ▸ hposition
    rw [List.getD_eq_getElem _ false hencoded]
    simp only [encoded, encodeScalar, List.getElem_ofFn]
  have hnat := congrArg BitVec.toNat hvector
  change (BitVec.ofBoolListLE encoded).toNat = value % 2 ^ bits
  simpa only [BitVec.toNat_cast, BitVec.toNat_ofNat] using hnat

theorem decodeScalar_encode_bounded (q value : Nat) (hvalue : value ≤ q) :
    decodeScalar (encodeScalar (width q) value) = value := by
  rw [decodeScalar_encodeScalar, Nat.mod_eq_of_lt (value_lt_two_pow_width q value hvalue)]

def encodeVector {size : Nat} (q : Nat) (capacity : Vector Nat size) : List Bool :=
  capacity.toArray.toList.flatMap (encodeScalar (width q))

def decodeVector (q size : Nat) (stream : List Bool) : Vector Nat size :=
  Vector.ofFn (fun index => decodeScalar ((stream.drop (index.val * width q)).take (width q)))

theorem encodeVector_length {size : Nat} (q : Nat) (capacity : Vector Nat size) :
    (encodeVector q capacity).length = size * width q := by
  simp only [encodeVector, List.length_flatMap, encodeScalar_length, List.map_const',
    List.sum_replicate, Array.length_toList, Vector.size_toArray, Nat.nsmul_eq_mul]

theorem fixedBlocks_slice {α : Type*} (block : α → List Bool) (bits : Nat)
    (hlength : ∀ value, (block value).length = bits) (entries : List α) (index : Nat)
    (hindex : index < entries.length) :
    ((entries.flatMap block).drop (index * bits)).take bits = block (entries[index]'hindex) := by
  induction entries generalizing index with
  | nil => simp only [List.length_nil] at hindex; omega
  | cons head later ih =>
    cases index with
    | zero =>
      simp only [List.flatMap_cons, Nat.zero_mul, List.drop_zero, List.getElem_cons_zero]
      exact List.take_left' (hlength head)
    | succ index =>
      have htail : index < later.length := Nat.lt_of_succ_lt_succ hindex
      have hmul : (index + 1) * bits = bits + index * bits := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [List.flatMap_cons, hmul, ← List.drop_drop (i := index * bits) (j := bits),
        List.drop_left' (hlength head), List.getElem_cons_succ]
      exact ih index htail

theorem decodeVector_encodeVector {size : Nat} (q : Nat) (capacity : Vector Nat size)
    (hbounded : ∀ index : Fin size, capacity.get index ≤ q) :
    decodeVector q size (encodeVector q capacity) = capacity := by
  apply Vector.ext
  intro index hindex
  change (Vector.ofFn _).get ⟨index, hindex⟩ = capacity.get ⟨index, hindex⟩
  rw [cache_get_ofFn]
  change decodeScalar (((capacity.toArray.toList.flatMap (encodeScalar (width q))).drop
    (index * width q)).take (width q)) = capacity.get ⟨index, hindex⟩
  have hlist : index < capacity.toArray.toList.length := by
    simpa only [Array.length_toList, Vector.size_toArray] using hindex
  rw [fixedBlocks_slice _ (width q) (encodeScalar_length (width q)) _ index hlist]
  have hvalue : capacity.toArray.toList[index]'hlist ≤ q := hbounded ⟨index, hindex⟩
  rw [decodeScalar_encode_bounded q _ hvalue]
  rfl

inductive Entry (size : Nat) where
  | void
  | vector (capacity : Vector Nat size)
  deriving DecidableEq

def Entry.Bounded {size : Nat} (q : Nat) : Entry size → Prop
  | .void => True
  | .vector capacity => ∀ index : Fin size, capacity.get index ≤ q

def encodeEntry {size : Nat} (q : Nat) : Entry size → List Bool
  | .void => [false]
  | .vector capacity => true :: encodeVector q capacity

def decodeEntry (q size : Nat) : List Bool → Option (Entry size)
  | [] => none
  | false :: [] => some .void
  | false :: _ :: _ => none
  | true :: payload =>
      if payload.length = size * width q then
        let capacity := decodeVector q size payload
        if ∀ index : Fin size, capacity.get index ≤ q then some (.vector capacity) else none
      else none

theorem encodeEntry_void_length (q size : Nat) :
    (encodeEntry q (.void : Entry size)).length = 1 := rfl

theorem encodeEntry_vector_length {size : Nat} (q : Nat) (capacity : Vector Nat size) :
    (encodeEntry q (.vector capacity)).length = 1 + size * width q := by
  rw [encodeEntry, List.length_cons, encodeVector_length, Nat.add_comm]

theorem decodeEntry_encodeEntry {size : Nat} (q : Nat) (entry : Entry size) (hbounded : entry.Bounded q) :
    decodeEntry q size (encodeEntry q entry) = some entry := by
  cases entry with
  | void => rfl
  | vector capacity =>
    change ∀ index : Fin size, capacity.get index ≤ q at hbounded
    simp only [encodeEntry, decodeEntry, encodeVector_length, ↓reduceIte,
      decodeVector_encodeVector q capacity hbounded]
    exact ite_eq_left hbounded

theorem encodeEntry_injective_bounded {size : Nat} (q : Nat) (left right : Entry size)
    (hleft : left.Bounded q) (hright : right.Bounded q) (heq : encodeEntry q left = encodeEntry q right) :
    left = right := by
  have hdecode := congrArg (decodeEntry q size) heq
  rw [decodeEntry_encodeEntry q left hleft, decodeEntry_encodeEntry q right hright] at hdecode
  exact Option.some.inj hdecode

theorem vector_encoding_ne_void {size : Nat} (q : Nat) (capacity : Vector Nat size) :
    encodeEntry q (.vector capacity) ≠ encodeEntry q (.void : Entry size) := by
  simp [encodeEntry]

def zeroVector (size : Nat) : Vector Nat size := Vector.ofFn (fun _ => 0)

theorem zeroVector_bounded (q size : Nat) : (Entry.vector (zeroVector size)).Bounded q := by
  intro index
  have hzero : (zeroVector size).get index = 0 := cache_get_ofFn _ _
  rw [hzero]
  exact Nat.zero_le _

theorem encodeVector_zero_q {size : Nat} (capacity : Vector Nat size) : encodeVector 0 capacity = [] := by
  apply List.length_eq_zero_iff.mp
  rw [encodeVector_length, width_zero, Nat.mul_zero]

theorem zero_q_vector_tag (size : Nat) : encodeEntry 0 (.vector (zeroVector size)) = [true] := by
  rw [encodeEntry, encodeVector_zero_q]

theorem zero_q_decode_vector (size : Nat) : decodeEntry 0 size [true] = some (.vector (zeroVector size)) := by
  rw [← zero_q_vector_tag size]
  exact decodeEntry_encodeEntry 0 _ (zeroVector_bounded 0 size)

def Entry.toCapacityEntry {size : Nat} : Entry size → CapacityEntry (Fin size)
  | .void => .void
  | .vector capacity => .vector capacity.get

def Entry.denote {Tool : Type*} [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (entry : Entry cache.nodes.size) : Set (Finset Tool) :=
  entry.toCapacityEntry.denote cache.capacityLayout

theorem decoded_entry_denote {Tool : Type*} [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (q : Nat) (entry : Entry cache.nodes.size) (hbounded : entry.Bounded q) :
    (decodeEntry q cache.nodes.size (encodeEntry q entry)).map (Entry.denote cache) = some (entry.denote cache) := by
  rw [decodeEntry_encodeEntry q entry hbounded]
  rfl

theorem zero_vector_denote_ne_void {Tool : Type*} [DecidableEq Tool] (cache : IndexedNodeCache Tool) :
    (Entry.vector (zeroVector cache.nodes.size)).denote cache ≠ (Entry.void : Entry cache.nodes.size).denote cache :=
  capacityEntry_vector_ne_void cache.capacityLayout _

/-- A dense binary value, separate from the host List representation. -/
def packStream (stream : List Bool) : BitVec stream.length := BitVec.ofBoolListLE stream

def unpackStream {bits : Nat} (packed : BitVec bits) : List Bool :=
  List.ofFn (fun position : Fin bits => packed.getLsbD position.val)

theorem unpackStream_packStream (stream : List Bool) : unpackStream (packStream stream) = stream := by
  apply List.ext_getElem
  · simp only [unpackStream, List.length_ofFn]
  · intro position _ hright
    simp only [unpackStream, List.getElem_ofFn, packStream, BitVec.getLsbD_ofBoolListLE]
    exact List.getD_eq_getElem _ false hright

theorem unpackStream_cast {left right : Nat} (packed : BitVec left) (heq : left = right) :
    unpackStream (packed.cast heq) = unpackStream packed := by
  cases heq
  rfl

def encodePackedVector {size : Nat} (q : Nat) (capacity : Vector Nat size) : BitVec (size * width q) :=
  (packStream (encodeVector q capacity)).cast (encodeVector_length q capacity)

def decodePackedVector (q size : Nat) (packed : BitVec (size * width q)) : Vector Nat size :=
  decodeVector q size (unpackStream packed)

theorem unpackPackedVector {size : Nat} (q : Nat) (capacity : Vector Nat size) :
    unpackStream (encodePackedVector q capacity) = encodeVector q capacity := by
  rw [encodePackedVector, unpackStream_cast, unpackStream_packStream]

theorem decodePackedVector_encodePackedVector {size : Nat} (q : Nat) (capacity : Vector Nat size)
    (hbounded : ∀ index : Fin size, capacity.get index ≤ q) :
    decodePackedVector q size (encodePackedVector q capacity) = capacity := by
  rw [decodePackedVector, unpackPackedVector, decodeVector_encodeVector q capacity hbounded]

def encodePackedEntry {size : Nat} (q : Nat) (entry : Entry size) : BitVec (encodeEntry q entry).length :=
  packStream (encodeEntry q entry)

def decodePackedEntry (q size : Nat) {bits : Nat} (packed : BitVec bits) : Option (Entry size) :=
  decodeEntry q size (unpackStream packed)

theorem decodePackedEntry_encodePackedEntry {size : Nat} (q : Nat) (entry : Entry size)
    (hbounded : entry.Bounded q) : decodePackedEntry q size (encodePackedEntry q entry) = some entry := by
  rw [decodePackedEntry, encodePackedEntry, unpackStream_packStream, decodeEntry_encodeEntry q entry hbounded]

/-- Self-delimiting entry parsing when the fixed size and q are known. -/
def decodeEntryPrefix (q size : Nat) : List Bool → Option (Entry size × List Bool)
  | [] => none
  | false :: remaining => some (.void, remaining)
  | true :: remaining =>
      if size * width q ≤ remaining.length then
        (decodeEntry q size (true :: remaining.take (size * width q))).map
          (fun entry => (entry, remaining.drop (size * width q)))
      else none

theorem decodeEntryPrefix_encode_append {size : Nat} (q : Nat) (entry : Entry size)
    (hbounded : entry.Bounded q) (remaining : List Bool) :
    decodeEntryPrefix q size (encodeEntry q entry ++ remaining) = some (entry, remaining) := by
  cases entry with
  | void => rfl
  | vector capacity =>
    have hlength := encodeVector_length q capacity
    have hspan : size * width q ≤ (encodeVector q capacity ++ remaining).length := by
      rw [List.length_append, hlength]
      omega
    have htake := List.take_left' (l₂ := remaining) hlength
    have hdrop := List.drop_left' (l₂ := remaining) hlength
    have hdecode : decodeEntry q size (true :: encodeVector q capacity) = some (.vector capacity) :=
      decodeEntry_encodeEntry q (.vector capacity) hbounded
    simp only [encodeEntry, List.cons_append, decodeEntryPrefix, hspan, ↓reduceIte, htake, hdrop,
      hdecode, Option.map_some]

def encodeEntries {size : Nat} (q : Nat) (entries : List (Entry size)) : List Bool := entries.flatMap (encodeEntry q)

def decodeEntriesPrefix (q size : Nat) : Nat → List Bool → Option (List (Entry size) × List Bool)
  | 0, remaining => some ([], remaining)
  | count + 1, stream => do
      let (entry, remaining) ← decodeEntryPrefix q size stream
      let (later, final) ← decodeEntriesPrefix q size count remaining
      return (entry :: later, final)

theorem decodeEntriesPrefix_encode_append {size : Nat} (q : Nat) (entries : List (Entry size))
    (hbounded : ∀ entry ∈ entries, entry.Bounded q) (remaining : List Bool) :
    decodeEntriesPrefix q size entries.length (encodeEntries q entries ++ remaining) = some (entries, remaining) := by
  revert hbounded remaining
  induction entries with
  | nil => intro _ _; rfl
  | cons entry later ih =>
    intro hbounded remaining
    have hhead := decodeEntryPrefix_encode_append q entry (hbounded entry List.mem_cons_self)
      (encodeEntries q later ++ remaining)
    have htail := ih (fun next hnext => hbounded next (List.mem_cons_of_mem _ hnext)) remaining
    change decodeEntriesPrefix q size (later.length + 1)
      ((encodeEntry q entry ++ encodeEntries q later) ++ remaining) = _
    rw [List.append_assoc]
    simp only [decodeEntriesPrefix, hhead, Option.bind_eq_bind, Option.bind_some, Option.pure_def, htail]

theorem encodeEntry_length_le {size : Nat} (q : Nat) (entry : Entry size) :
    (encodeEntry q entry).length ≤ 1 + size * width q := by
  cases entry with
  | void => simp only [encodeEntry_void_length]; omega
  | vector capacity => exact Nat.le_of_eq (encodeEntry_vector_length q capacity)

theorem encodeEntries_length_le {size : Nat} (q : Nat) (entries : List (Entry size)) :
    (encodeEntries q entries).length ≤ entries.length * (1 + size * width q) := by
  induction entries with
  | nil => simp only [encodeEntries, List.flatMap_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons entry later ih =>
    change (encodeEntry q entry ++ encodeEntries q later).length ≤ _
    rw [List.length_append]
    calc
      _ ≤ (1 + size * width q) + later.length * (1 + size * width q) :=
        Nat.add_le_add (encodeEntry_length_le q entry) ih
      _ = (entry :: later).length * (1 + size * width q) := by
        rw [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem decodePackedEntries_encodeEntries {size : Nat} (q : Nat) (entries : List (Entry size))
    (hbounded : ∀ entry ∈ entries, entry.Bounded q) :
    decodeEntriesPrefix q size entries.length (unpackStream (packStream (encodeEntries q entries))) =
      some (entries, []) := by
  rw [unpackStream_packStream]
  simpa only [List.append_nil] using decodeEntriesPrefix_encode_append q entries hbounded []

end PaperProofs.Structure.LaminarTree.CapacityBits
