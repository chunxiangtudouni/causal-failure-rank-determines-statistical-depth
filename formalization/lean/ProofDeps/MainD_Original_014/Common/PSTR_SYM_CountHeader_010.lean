module

public import Common.PSTR_SYM_NaturalScanRuns_009

/-! Real original outer count-header parsing followed by the actual
Natural-Datum loop. The count is read from its original binary encoding;
it is not a program parameter or a supplied iteration count. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator

open Turing PA17TMRatArithmeticParse002
open PSTRTMSeq005

def outerLeft (left : List Bool) (count : Nat) : List Bool :=
  false :: (PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload count).reverse ++ left)

def locatorMachine : Machine 36 := PSTRTMSeq005.seqMachine streamMachine scanMachine

def locatorTrace (left : List Bool) (count : Nat) (numbers : List Nat) (suffix : List Bool) :
    List (MachineState 36) :=
  (streamTrace left [] (PSTRTMNatValue017.rawPayload count)
    (naturalPrefix numbers ++ true :: suffix)).map (PSTRTMSeq005.leftCfg (b := 18)) ++
  (scanTrace (outerLeft left count) numbers suffix).map (PSTRTMSeq005.rightCfg (a := 17))

def locatorFinal (left : List Bool) (count : Nat) (numbers : List Nat) (suffix : List Bool) :
    MachineState 36 := PSTRTMSeq005.rightCfg (a := 17) (scanFinal (outerLeft left count) numbers suffix)

theorem locator_runsFrom (left : List Bool) (count : Nat) (numbers : List Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom locatorMachine
      ⟨0,Tape.mk₂ left (encodeNat count ++ (naturalPrefix numbers ++ true :: suffix))⟩
      (locatorTrace left count numbers suffix) (locatorFinal left count numbers suffix) := by
  have header := encodeNat_stream_runsFrom left (naturalPrefix numbers ++ true :: suffix) count
  have body := scan_runsFrom (outerLeft left count) numbers suffix
  unfold locatorMachine locatorTrace locatorFinal
  exact PSTRTMSeq005.seq_runsFrom streamMachine scanMachine
    (streamState 0 left (encodeNat count ++ (naturalPrefix numbers ++ true :: suffix)))
    (streamFinal left (PSTRTMNatValue017.rawPayload count) (naturalPrefix numbers ++ true :: suffix))
    (scanFinal (outerLeft left count) numbers suffix)
    (streamTrace left [] (PSTRTMNatValue017.rawPayload count) (naturalPrefix numbers ++ true :: suffix))
    (scanTrace (outerLeft left count) numbers suffix) header body

theorem locator_final_tape (left : List Bool) (count : Nat) (numbers : List Nat) (suffix : List Bool) :
    (locatorFinal left count numbers suffix).Tape =
      Tape.mk₂ (scanArchive (outerLeft left count) numbers) (true :: suffix) := rfl

/-- A bound on the actual concatenated trace, including the genuine
parser-HALT transfer into scanMachine. -/
theorem locator_time_le (left : List Bool) (count : Nat) (numbers : List Nat) (suffix : List Bool) :
    (locatorTrace left count numbers suffix).length ≤
      32 * ((encodeNat count).length + (naturalPrefix numbers).length + 1)^2 := by
  have header := stream_length_le left (PSTRTMNatValue017.rawPayload count)
    (naturalPrefix numbers ++ true :: suffix)
  rw [rawPayload_length] at header
  have body := scan_time_le (outerLeft left count) numbers suffix
  have first : natBits count + 1 ≤ (encodeNat count).length + (naturalPrefix numbers).length + 1 := by
    rw [PSTRTMLength004.encodeNat_length]
    omega
  have second : (naturalPrefix numbers).length + 1 ≤
      (encodeNat count).length + (naturalPrefix numbers).length + 1 := by omega
  have hf := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left first 2)
  have hs := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left second 2)
  simp only [locatorTrace, List.length_append, List.length_map]
  omega

theorem locator_space_le (inputLength : Nat) (left : List Bool) (count : Nat)
    (numbers : List Nat) (suffix : List Bool) :
    visitedSpace locatorMachine inputLength (locatorTrace left count numbers suffix) ≤
      inputLength + 64 * ((encodeNat count).length + (naturalPrefix numbers).length + 1)^2 + 1 := by
  have cells := PSTRTMTrace002.visitedSpace_le locatorMachine inputLength (locatorTrace left count numbers suffix)
  have clock := locator_time_le left count numbers suffix
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator

