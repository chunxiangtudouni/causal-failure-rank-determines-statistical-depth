module

public import Paid.PDROC_BitVM_Common_IO_Output_Back_007
public import Paid.PDROC_BitVM_Common_IO_Output_Canonical_010
public import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing
open PaperProofs.Common.Native.PSTRWordBool

attribute [local implicit_reducible] Turing.TM2to1.Γ'

/-- A fixed32-pair description of the EXISTING Root encoding. This is
not a replacement codec, program input, or finite machine Store. -/
def trackPairs (row : Wide.VMTrack) : List (Bool × Bool) :=
  List.ofFn (fun slot : Fin 32 => ((row.2 slot).isSome, (row.2 slot).getD false))

theorem trackPairs_length (row : Wide.VMTrack) : (trackPairs row).length = 32 := by simp [trackPairs]

theorem encode_row_pairs (row : Wide.VMTrack) :
    (FiniteTrackCodec.encode row).toList = row.1 :: pairBits (trackPairs row) := by
  have encodedLength : (FiniteTrackCodec.encode row).toList.length = 65 := List.Vector.toList_length _
  apply List.ext_getElem
  · rw [encodedLength]
    simp [pairBits_length, trackPairs_length]
  · intro index inside _
    have cap : index < 65 := by simpa only [encodedLength] using inside
    interval_cases index <;> rfl

theorem trackPairs_some (row : Wide.VMTrack) (slot : Fin 32) (bit : Bool)
    (value : row.2 slot = some bit) : pairFound (trackPairs row) = true := by
  apply List.any_eq_true.mpr
  refine ⟨((row.2 slot).isSome, (row.2 slot).getD false), ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨slot, rfl⟩
  · simp [value]

theorem trackPairs_blank : pairFound (trackPairs (default : Wide.VMTrack)) = false := rfl

def scannedStore (saved : Store) (seen : Bool) : Store := { saved with seen := seen }

theorem findEnd_occupied (saved : Store) (pairs : List (Bool × Bool)) (width : pairs.length = 32)
    (occupied : pairFound pairs = true) (left suffix : List Bool) :
    TM1.step program (cfg 2 saved (Tape.mk₂ left (false :: (pairBits pairs ++ suffix)))) =
      some (cfg 2 (scannedStore saved true)
        (Tape.mk₂ ((false :: pairBits pairs).reverse ++ left) suffix)) := by
  let next : Statement := .move .right (.branch (fun _ saved => saved.seen)
      (.goto (fun _ _ => 2))
      (Wide.moveCode .left 65 (.write (fun _ _ => true)
        (Wide.moveCode .right 4 (.goto (fun _ _ => 4))))))
  have probed := presenceCode_correct pairs false left suffix { saved with seen := false } next
  rw [width] at probed
  change some (TM1.stepAux (presenceCode 32 next)
    { saved with seen := false } (Tape.mk₂ left (false :: (pairBits pairs ++ suffix)))) = _
  rw [probed]
  dsimp only [next]
  simp only [TM1.stepAux, presenceTape_right, seenStore, occupied]
  rfl

/-- Genuine full-row empty observation followed by actual rewind,
anchor write and move to the first output flag. It does not erase any
other cell: the caller derives ALL-empty-tail from the real projection. -/
theorem findEnd_empty (saved : Store) (pairs : List (Bool × Bool)) (width : pairs.length = 32)
    (empty : pairFound pairs = false) (left suffix : List Bool) :
    TM1.step program (cfg 2 saved (Tape.mk₂ left (false :: (pairBits pairs ++ suffix)))) =
      some (cfg 4 (scannedStore saved false)
        ((fun old : Tape Bool => old.move .right)^[4]
          (Tape.mk₂ left (true :: (pairBits pairs ++ suffix))))) := by
  let afterWrite : Statement := .write (fun _ _ => true) (Wide.moveCode .right 4 (.goto (fun _ _ => 4)))
  have moved := Wide.moveCode_left (false :: pairBits pairs).reverse left suffix
    (scannedStore saved false) afterWrite
  have length : (false :: pairBits pairs).reverse.length = 65 := by
    simp [pairBits_length, width]
  rw [length] at moved
  let next : Statement := .move .right (.branch (fun _ saved => saved.seen)
      (.goto (fun _ _ => 2)) (Wide.moveCode .left 65 afterWrite))
  have probed := presenceCode_correct pairs false left suffix { saved with seen := false } next
  rw [width] at probed
  change some (TM1.stepAux (presenceCode 32 next)
    { saved with seen := false } (Tape.mk₂ left (false :: (pairBits pairs ++ suffix)))) = _
  rw [probed]
  dsimp only [next]
  simp only [TM1.stepAux, presenceTape_right, seenStore, empty]
  change some (TM1.stepAux (Wide.moveCode .left 65 afterWrite) (scannedStore saved false)
    (Tape.mk₂ ((false :: pairBits pairs).reverse ++ left) suffix)) = _
  rw [moved]
  simp only [List.reverse_reverse]
  change some (TM1.stepAux (Wide.moveCode .right 4 (.goto (fun _ _ => 4))) (scannedStore saved false)
    (Tape.mk₂ left (true :: (pairBits pairs ++ suffix)))) = _
  rw [Wide.moveCode_semantics]
  rfl

end PDROC.BitVM.Common.IO.Output
