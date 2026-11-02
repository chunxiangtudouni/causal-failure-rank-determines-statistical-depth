module

public import Common.PSTR_WordBool_PushPopTM1_003

/-! An explicit pointed five-bit alphabet code. Presence bits distinguish
empty stacks from stored false bits. This is the compiler's physical track
code, not an uncharged adapter from ORIGINAL RCC input. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.TrackCodec

open Turing

abbrev Track := PushPopTM1.Track

def encode (row : Track) : List.Vector Bool 5 :=
  ⟨[row.1, (row.2 0).isSome, (row.2 0).getD false,
    (row.2 1).isSome, (row.2 1).getD false], rfl⟩

def decode (bits : List.Vector Bool 5) : Track :=
  (bits.get 0, fun stack => if stack = 0 then
    if bits.get 1 then some (bits.get 2) else none
  else if bits.get 3 then some (bits.get 4) else none)

theorem encode_default : encode default = List.Vector.replicate 5 false := rfl

theorem decode_encode (row : Track) : decode (encode row) = row := by
  obtain ⟨bottom, cells⟩ := row
  apply Prod.ext
  · rfl
  · funext stack
    fin_cases stack
    · cases cell : cells 0 with
      | none => simp [decode, encode, List.Vector.get, cell]
      | some bit => simp [decode, encode, List.Vector.get, cell]
    · cases cell : cells 1 with
      | none => simp [decode, encode, List.Vector.get, cell]
      | some bit => simp [decode, encode, List.Vector.get, cell]

def encodedInput (input : List Bool) : List Bool :=
  (TM2to1.trInit (0 : PushPop.Stack) input).flatMap (fun row => (encode row).toList)

theorem encoded_length (input : List Bool) :
    (encodedInput input).length =
      5 * (TM2to1.trInit (Γ := PushPop.Alphabet) (0 : PushPop.Stack) input).length := by
  unfold encodedInput
  induction TM2to1.trInit (Γ := PushPop.Alphabet) (0 : PushPop.Stack) input with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.length_append, List.Vector.toList_length,
      List.length_cons, ih]
    omega

def compiled : TM1to1.Λ' Track PushPopTM1.Label Unit →
    TM1.Stmt Bool (TM1to1.Λ' Track PushPopTM1.Label Unit) Unit :=
  TM1to1.tr encode decode PushPopTM1.compiled

theorem supports : TM1.Supports compiled
    (TM1to1.trSupp PushPopTM1.compiled (TM2to1.trSupp PushPop.program Finset.univ)) :=
  TM1to1.tr_supports encode decode PushPopTM1.compiled PushPopTM1.supports

end PaperProofs.Common.Native.PSTRWordBool.TrackCodec
