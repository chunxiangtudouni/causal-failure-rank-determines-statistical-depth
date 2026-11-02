module

public import Common.PSTR_WordBool_FiniteTrackCodec_030
public import PaperProofs.Common.RationalControllerComputation

/-! The exact physical target for the raw-input front. These identities do
not supply a machine, a trace, a length input, or a charged adapter. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

def rowBits (bottom bit : Bool) : List Bool :=
  bottom :: true :: bit :: List.replicate 30 false

def inputTrack (bottom bit : Bool) : FiniteTrackCodec.Track 16 :=
  (bottom, Function.update (fun _ : Fin 16 => (none : Option Bool)) 0 (some bit))

theorem row_encoding (bottom bit : Bool) :
    (FiniteTrackCodec.encode (inputTrack bottom bit)).toList = rowBits bottom bit := by
  cases bottom <;> cases bit <;> rfl

theorem rowBits_length (bottom bit : Bool) : (rowBits bottom bit).length = 33 := by
  rfl

def rawPrefix (data : List Datum) : List Bool :=
  encodeNat data.length ++ data.flatMap encodeDatum

theorem raw_input_eq (data : List Datum) :
    encode data = rawPrefix data ++ [true] := rfl

theorem raw_input_length (data : List Datum) :
    (encode data).length = (rawPrefix data).length + 1 := by
  rw [raw_input_eq, List.length_append]
  rfl

theorem raw_input_nonempty (data : List Datum) : encode data ≠ [] := by
  intro empty
  have size := congrArg List.length empty
  rw [raw_input_length] at size
  simp only [List.length_nil] at size
  omega

theorem encoded_footer_shape (frontBits : List Bool) :
    FiniteTrackCodec.encodedInput (0 : Fin 16) (frontBits ++ [true]) =
      rowBits true true ++ frontBits.reverse.flatMap (rowBits false) := by
  have reversed : (frontBits ++ [true]).reverse = true :: frontBits.reverse := by
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append]
  unfold FiniteTrackCodec.encodedInput TM2to1.trInit
  rw [reversed]
  change (FiniteTrackCodec.encode (inputTrack true true)).toList ++
      (frontBits.reverse.map (inputTrack false)).flatMap
        (fun row => (FiniteTrackCodec.encode row).toList) = _
  rw [row_encoding, List.flatMap_map]
  simp only [row_encoding]

theorem encoded_raw_shape (data : List Datum) :
    FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data) =
      rowBits true true ++ (rawPrefix data).reverse.flatMap (rowBits false) := by
  rw [raw_input_eq]
  exact encoded_footer_shape (rawPrefix data)

theorem rows_length (bits : List Bool) :
    (bits.flatMap (rowBits false)).length = 33 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [List.flatMap_cons, List.length_append, rowBits_length,
      List.length_cons, ih]
    omega

theorem encoded_raw_length (data : List Datum) :
    (FiniteTrackCodec.encodedInput (0 : Fin 16) (encode data)).length =
      33 * (encode data).length := by
  rw [encoded_raw_shape, List.length_append, rowBits_length, rows_length,
    List.length_reverse, raw_input_length]
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit
