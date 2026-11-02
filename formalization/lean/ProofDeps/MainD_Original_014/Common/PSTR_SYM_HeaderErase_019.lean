module

public import Common.PSTR_SYM_NaturalErase_018

/-! A real count-header parser followed by the fixed Natural erasing loop.
The count stays as an actual flagged record; the original data strip is
really cleared and the head reaches its real TRUE tag. There is no EOF
assertion for an arbitrary TRUE suffix and no completed output serializer. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicHeaderErase

open Turing PSTRTMSeq005 PA17TMRatArithmeticParse002
open PSTRSymbolicLocator (naturalPrefix outerLeft rawPayload_length)

def headerEraseMachine : Machine 46 := seqMachine streamMachine PSTRSymbolicNaturalErase.eraseMachine

def headerEraseTrace (left : List Bool) (count : Nat) (numbers : List Nat) (suffix : List Bool) :
    List (MachineState 46) :=
  (streamTrace left [] (PSTRTMNatValue017.rawPayload count)
    (naturalPrefix numbers ++ true :: suffix)).map (leftCfg (b := 28)) ++
      (PSTRSymbolicNaturalErase.eraseTrace (outerLeft left count) numbers suffix).map (rightCfg (a := 17))

def headerEraseFinal (left : List Bool) (count : Nat) (numbers : List Nat) (suffix : List Bool) :
    MachineState 46 :=
  rightCfg (a := 17) (PSTRSymbolicNaturalErase.eraseFinal (outerLeft left count) numbers suffix)

theorem headerErase_runsFrom (left : List Bool) (count : Nat) (numbers : List Nat) (suffix : List Bool) :
    RunsFrom headerEraseMachine
      ⟨0, Tape.mk₂ left (encodeNat count ++ (naturalPrefix numbers ++ true :: suffix))⟩
      (headerEraseTrace left count numbers suffix) (headerEraseFinal left count numbers suffix) := by
  have header := encodeNat_stream_runsFrom left (naturalPrefix numbers ++ true :: suffix) count
  have body := PSTRSymbolicNaturalErase.erase_runsFrom (outerLeft left count) numbers suffix
  unfold headerEraseMachine headerEraseTrace headerEraseFinal
  exact seq_runsFrom streamMachine PSTRSymbolicNaturalErase.eraseMachine
    ⟨0, Tape.mk₂ left (encodeNat count ++ (naturalPrefix numbers ++ true :: suffix))⟩
    (streamFinal left (PSTRTMNatValue017.rawPayload count) (naturalPrefix numbers ++ true :: suffix))
    (PSTRSymbolicNaturalErase.eraseFinal (outerLeft left count) numbers suffix)
    (streamTrace left [] (PSTRTMNatValue017.rawPayload count) (naturalPrefix numbers ++ true :: suffix))
    (PSTRSymbolicNaturalErase.eraseTrace (outerLeft left count) numbers suffix) header body

theorem headerErase_final_tape (left : List Bool) (count : Nat) (numbers : List Nat) (suffix : List Bool) :
    (headerEraseFinal left count numbers suffix).Tape =
      Tape.mk₂ (List.replicate (naturalPrefix numbers).length false ++ outerLeft left count) (true :: suffix) := by
  simp only [headerEraseFinal, rightCfg, PSTRSymbolicNaturalErase.erase_final_tape]

theorem headerErase_time_le (left : List Bool) (count : Nat) (numbers : List Nat) (suffix : List Bool) :
    (headerEraseTrace left count numbers suffix).length ≤
      64 * ((encodeNat count).length + (naturalPrefix numbers).length + 1)^2 := by
  have header := stream_length_le left (PSTRTMNatValue017.rawPayload count)
    (naturalPrefix numbers ++ true :: suffix)
  rw [rawPayload_length] at header
  have body := PSTRSymbolicNaturalErase.erase_time_le (outerLeft left count) numbers suffix
  have first : natBits count + 1 ≤ (encodeNat count).length + (naturalPrefix numbers).length + 1 := by
    rw [PSTRTMLength004.encodeNat_length]
    omega
  have second : (naturalPrefix numbers).length + 1 ≤
      (encodeNat count).length + (naturalPrefix numbers).length + 1 := by omega
  have hf := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left first 2)
  have hs := Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left second 2)
  simp only [headerEraseTrace, List.length_append, List.length_map]
  omega

theorem headerErase_space_le (inputLength : Nat) (left : List Bool) (count : Nat)
    (numbers : List Nat) (suffix : List Bool) :
    visitedSpace headerEraseMachine inputLength (headerEraseTrace left count numbers suffix) ≤
      inputLength + 128 * ((encodeNat count).length + (naturalPrefix numbers).length + 1)^2 + 1 := by
  have cells := PSTRTMTrace002.visitedSpace_le headerEraseMachine inputLength
    (headerEraseTrace left count numbers suffix)
  have clock := headerErase_time_le left count numbers suffix
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicHeaderErase
