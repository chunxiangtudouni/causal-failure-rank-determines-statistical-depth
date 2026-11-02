module

public import Common.PSTR_WordBool_TrackCodec_004

/-! Pointed track codecs for a FIXED compile-time number of Bool stacks.
Fin5/Fin16 use actual11/33-bit rows. The stack count is chosen before inputs;
it is not runtime word width, a heap bound, or a new original input field. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.FiniteTrackCodec

open Turing

abbrev Track (count : Nat) := TM2to1.Γ' (Fin count) (fun _ => Bool)

def width (count : Nat) : Nat := 2 * count + 1

def bottomIndex (count : Nat) : Fin (width count) := ⟨0, by unfold width; omega⟩

def presenceIndex {count : Nat} (slot : Fin count) : Fin (width count) :=
  ⟨2 * slot.val + 1, by have bound := slot.isLt; unfold width; omega⟩

def valueIndex {count : Nat} (slot : Fin count) : Fin (width count) :=
  ⟨2 * slot.val + 2, by have bound := slot.isLt; unfold width; omega⟩

def encode {count : Nat} (row : Track count) : List.Vector Bool (width count) :=
  List.Vector.ofFn fun position =>
    if zero : position.val = 0 then row.1 else
      let slot : Fin count := ⟨(position.val - 1) / 2, by
        have bound := position.isLt
        dsimp only [width] at bound
        omega⟩
      if (position.val - 1) % 2 = 0 then (row.2 slot).isSome else (row.2 slot).getD false

def decode {count : Nat} (bits : List.Vector Bool (width count)) : Track count :=
  (bits.get (bottomIndex count), fun slot =>
    if bits.get (presenceIndex slot) then some (bits.get (valueIndex slot)) else none)

theorem encode_bottom {count : Nat} (row : Track count) :
    (encode row).get (bottomIndex count) = row.1 := by
  simp only [encode, List.Vector.get_ofFn, bottomIndex, dite_true]

theorem encode_presence {count : Nat} (row : Track count) (slot : Fin count) :
    (encode row).get (presenceIndex slot) = (row.2 slot).isSome := by
  have nonzero : 2 * slot.val + 1 ≠ 0 := by omega
  have quotient : (2 * slot.val + 1 - 1) / 2 = slot.val := by omega
  have parity : (2 * slot.val + 1 - 1) % 2 = 0 := by omega
  simp only [encode, List.Vector.get_ofFn, presenceIndex, dite_eq_right nonzero,
    ite_eq_left parity, quotient]

theorem encode_value {count : Nat} (row : Track count) (slot : Fin count) :
    (encode row).get (valueIndex slot) = (row.2 slot).getD false := by
  have nonzero : 2 * slot.val + 2 ≠ 0 := by omega
  have quotient : (2 * slot.val + 2 - 1) / 2 = slot.val := by omega
  have parity : (2 * slot.val + 2 - 1) % 2 ≠ 0 := by omega
  simp only [encode, List.Vector.get_ofFn, valueIndex, dite_eq_right nonzero,
    ite_eq_right parity, quotient]

theorem decode_encode {count : Nat} (row : Track count) : decode (encode row) = row := by
  apply Prod.ext
  · exact encode_bottom row
  · funext slot
    change (if (encode row).get (presenceIndex slot) then
      some ((encode row).get (valueIndex slot)) else none) = row.2 slot
    rw [encode_presence, encode_value]
    cases datum : row.2 slot with
    | none => rfl
    | some bit => rfl

theorem encode_default (count : Nat) :
    encode (default : Track count) = List.Vector.replicate (width count) false := by
  change encode (show Track count from (false, fun _ => none)) = _
  apply List.Vector.ext
  intro position
  rw [List.Vector.get_replicate]
  simp only [encode, List.Vector.get_ofFn]
  by_cases zero : position.val = 0
  · simp only [dite_eq_left zero]
  · by_cases parity : (position.val - 1) % 2 = 0
    · simp only [dite_eq_right zero, ite_eq_left parity]; rfl
    · simp only [dite_eq_right zero, ite_eq_right parity]; rfl

def encodedInput {count : Nat} (inputSlot : Fin count) (input : List Bool) : List Bool :=
  (TM2to1.trInit (Γ := fun _ : Fin count => Bool) inputSlot input).flatMap (fun row => (encode row).toList)

theorem encoded_length {count : Nat} (inputSlot : Fin count) (input : List Bool) :
    (encodedInput inputSlot input).length = width count *
      (TM2to1.trInit (Γ := fun _ : Fin count => Bool) inputSlot input).length := by
  unfold encodedInput
  induction TM2to1.trInit (Γ := fun _ : Fin count => Bool) inputSlot input with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.length_append, List.Vector.toList_length,
      List.length_cons, ih]
    exact (Nat.add_comm _ _).trans (Nat.mul_succ (width count) tail.length).symm

end PaperProofs.Common.Native.PSTRWordBool.FiniteTrackCodec
