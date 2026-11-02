module

public import Paid.PDROC_BitVM_Common_IO_Wide_Primitives_001
public import Common.PSTR_WordBool_FiniteTrackCodec_030

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 5000
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing
open PaperProofs.Common.Native.PSTRWordBool

attribute [local implicit_reducible] Turing.TM2to1.Γ'

abbrev VMStack := Fin 32
abbrev VMTrack := FiniteTrackCodec.Track 32

/-- Only the input-row compatibility fact is new. The actual pointed
encoder, decoder, inverse and default proofs are Root030's existing APIs. -/
def inputTrack (bottom bit : Bool) : VMTrack :=
  (bottom, Function.update (fun _ => none) (0 : VMStack) (some bit))

def cleanVector (bottom bit : Bool) : List.Vector Bool (FiniteTrackCodec.width 32) :=
  ⟨cleanRow 29 bottom bit, by simp [cleanRow, padding, FiniteTrackCodec.width]⟩

theorem encode_inputTrack (bottom bit : Bool) :
    FiniteTrackCodec.encode (inputTrack bottom bit) = cleanVector bottom bit := by
  cases bottom <;> cases bit <;> rfl

def encodedInit32 (input : List Bool) : List Bool :=
  FiniteTrackCodec.encodedInput (0 : VMStack) input

/-- The actual target has original LAST bit in its first bottom-marked
row. This is exactly the physical reverse-prepend bootloader's target. -/
theorem encodedInit32_snoc (word : List Bool) (last : Bool) :
    encodedInit32 (word ++ [last]) =
      cleanRow 29 true last ++ word.reverse.flatMap (cleanRow 29 false) := by
  simp only [encodedInit32, FiniteTrackCodec.encodedInput, TM2to1.trInit, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  change (FiniteTrackCodec.encode (inputTrack true last)).toList ++
    (word.reverse.map (inputTrack false)).flatMap (fun row => (FiniteTrackCodec.encode row).toList) = _
  simp only [List.flatMap_map, encode_inputTrack, cleanVector]
  rfl

end PDROC.BitVM.Common.IO.Wide
