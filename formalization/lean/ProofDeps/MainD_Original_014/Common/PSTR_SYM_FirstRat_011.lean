module

public import Common.PSTR_SYM_CountHeader_010
public import Structure.PA17_TM_RatArithmetic_Parse_002e

/-! One fixed83-label original Bool parser locates the first genuine Rat
after an outer count and Natural prefix, then physically parses that Rat.
This local port does not supply the original N0/all-stage/outer-EOF branches. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator

open Turing PA17TMRatArithmeticParse002

def ratTail (value : Rat) (suffix : List Bool) : List Bool :=
  sign value :: (rawField (numeratorDigits value) ++ (rawField (denominatorDigits value) ++ suffix))

theorem ratTail_encoding (value : Rat) (suffix : List Bool) :
    true :: ratTail value suffix = encodeDatum (.rational value) ++ suffix := by
  rw [rational_datum]
  simp only [ratTail, List.cons_append, List.nil_append, List.append_assoc]

def firstRatArchive (left : List Bool) (count : Nat) (numbers : List Nat) : List Bool :=
  scanArchive (outerLeft left count) numbers

def firstRatMachine : Machine 82 := PSTRTMSeq005.seqMachine locatorMachine ratMachine

def firstRatTrace (left : List Bool) (count : Nat) (numbers : List Nat)
    (value : Rat) (suffix : List Bool) : List (MachineState 82) :=
  (locatorTrace left count numbers (ratTail value suffix)).map (PSTRTMSeq005.leftCfg (b := 45)) ++
  (ratTrace (firstRatArchive left count numbers) (sign value)
    (numeratorDigits value) (denominatorDigits value) suffix).map (PSTRTMSeq005.rightCfg (a := 36))

def firstRatFinal (left : List Bool) (count : Nat) (numbers : List Nat)
    (value : Rat) (suffix : List Bool) : MachineState 82 :=
  PSTRTMSeq005.rightCfg (a := 36) (ratFinal (firstRatArchive left count numbers) (sign value)
    (numeratorDigits value) (denominatorDigits value) suffix)

theorem firstRat_runsFrom (left : List Bool) (count : Nat) (numbers : List Nat)
    (value : Rat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom firstRatMachine
      ⟨0,Tape.mk₂ left (encodeNat count ++ (naturalPrefix numbers ++ encodeDatum (.rational value) ++ suffix))⟩
      (firstRatTrace left count numbers value suffix) (firstRatFinal left count numbers value suffix) := by
  have located := locator_runsFrom left count numbers (ratTail value suffix)
  have parsed := encodeDatum_rat_runsFrom (firstRatArchive left count numbers) suffix value
  have sameInput : (locatorFinal left count numbers (ratTail value suffix)).Tape =
      Tape.mk₂ (firstRatArchive left count numbers) (encodeDatum (.rational value) ++ suffix) := by
    rw [locator_final_tape, ratTail_encoding]
    rfl
  have next : PSTRTMSeq005.RunsFrom ratMachine
      ⟨0,(locatorFinal left count numbers (ratTail value suffix)).Tape⟩
      (ratTrace (firstRatArchive left count numbers) (sign value)
        (numeratorDigits value) (denominatorDigits value) suffix)
      (ratFinal (firstRatArchive left count numbers) (sign value)
        (numeratorDigits value) (denominatorDigits value) suffix) := by
    rw [sameInput]
    exact parsed
  have joined := PSTRTMSeq005.seq_runsFrom locatorMachine ratMachine
    (⟨0,Tape.mk₂ left (encodeNat count ++ (naturalPrefix numbers ++ true :: ratTail value suffix))⟩ : MachineState 36)
    (locatorFinal left count numbers (ratTail value suffix))
    (ratFinal (firstRatArchive left count numbers) (sign value)
      (numeratorDigits value) (denominatorDigits value) suffix)
    (locatorTrace left count numbers (ratTail value suffix))
    (ratTrace (firstRatArchive left count numbers) (sign value)
      (numeratorDigits value) (denominatorDigits value) suffix) located next
  simpa [firstRatMachine, firstRatTrace, firstRatFinal, PSTRTMSeq005.leftCfg,
    PSTRTMSeq005.leftLabel, ratTail_encoding, List.append_assoc] using joined

theorem firstRat_final_tape (left : List Bool) (count : Nat) (numbers : List Nat)
    (value : Rat) (suffix : List Bool) :
    (firstRatFinal left count numbers value suffix).Tape =
      Tape.mk₂ (ratLeft (firstRatArchive left count numbers) value) suffix := rfl

theorem rat_trace_time (left : List Bool) (value : Rat) (suffix : List Bool) :
    (ratTrace left (sign value) (numeratorDigits value) (denominatorDigits value) suffix).length ≤
      16 * ((encodeDatum (.rational value)).length + 1)^2 := by
  rw [ratTrace_length, datum_length]
  nlinarith [Nat.zero_le ((numeratorDigits value).length * (denominatorDigits value).length)]

theorem firstRat_time_le (left : List Bool) (count : Nat) (numbers : List Nat)
    (value : Rat) (suffix : List Bool) :
    (firstRatTrace left count numbers value suffix).length ≤
      64 * ((encodeNat count).length + (naturalPrefix numbers).length +
        (encodeDatum (.rational value)).length + 1)^2 := by
  have located := locator_time_le left count numbers (ratTail value suffix)
  have parsed := rat_trace_time (firstRatArchive left count numbers) value suffix
  have first : (encodeNat count).length + (naturalPrefix numbers).length + 1 ≤
      (encodeNat count).length + (naturalPrefix numbers).length + (encodeDatum (.rational value)).length + 1 := by omega
  have second : (encodeDatum (.rational value)).length + 1 ≤
      (encodeNat count).length + (naturalPrefix numbers).length + (encodeDatum (.rational value)).length + 1 := by omega
  have hf := Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left first 2)
  have hs := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left second 2)
  simp only [firstRatTrace, List.length_append, List.length_map]
  omega

theorem firstRat_space_le (inputLength : Nat) (left : List Bool) (count : Nat)
    (numbers : List Nat) (value : Rat) (suffix : List Bool) :
    visitedSpace firstRatMachine inputLength (firstRatTrace left count numbers value suffix) ≤
      inputLength + 128 * ((encodeNat count).length + (naturalPrefix numbers).length +
        (encodeDatum (.rational value)).length + 1)^2 + 1 := by
  have cells := PSTRTMTrace002.visitedSpace_le firstRatMachine inputLength
    (firstRatTrace left count numbers value suffix)
  have clock := firstRat_time_le left count numbers value suffix
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator
