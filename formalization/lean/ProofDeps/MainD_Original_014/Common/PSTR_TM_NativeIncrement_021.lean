module
public import Common.PSTR_TM_Canonical_020

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeIncrement021
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009 PSTRTMUnblock018 PSTRTMUnblockTrace019 PSTRTMNatValue017 PSTRTMCanonical020

/-- The full fixed52-label Bool program: original raw input expansion,
binary carry, then actual contraction to the original raw output format. -/
def nativeIncrementMachine : Machine 51 :=
  PSTRTMSeq005.seqMachine PSTRTMRawNat010.rawIncrementMachine unblockMachine

def nativeTrace (digits : List Bool) : List (MachineState 51) :=
  (PSTRTMRawNat010.rawIncrementTrace digits).map (PSTRTMSeq005.leftCfg (b := 19)) ++
    (unblockTrace (bumpDigits digits)).map (PSTRTMSeq005.rightCfg (a := 31))

def nativeFinal (digits : List Bool) : MachineState 51 :=
  PSTRTMSeq005.rightCfg (a := 31) (PSTRTMUnblock018.state 19 [false] (PSTRTMUnblockTrace019.rawWord (bumpDigits digits)))

theorem increment_final_tape (digits : List Bool) :
    (PSTRTMRawNat010.rawIncrementFinal digits).Tape = Turing.Tape.mk₁ (blocks (bumpDigits digits)) := by
  simp only [PSTRTMRawNat010.rawIncrementFinal, PSTRTMSeq005.rightCfg,
    PSTRTMIncrement009.state, Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]

theorem native_runs (digits : List Bool) :
    Runs nativeIncrementMachine (PSTRTMUnblockTrace019.rawWord digits) (nativeTrace digits) (nativeFinal digits) := by
  apply PSTRTMSeq005.seq_runs PSTRTMRawNat010.rawIncrementMachine unblockMachine (PSTRTMUnblockTrace019.rawWord digits)
    (PSTRTMRawNat010.rawIncrementFinal digits) (PSTRTMUnblock018.state 19 [false] (PSTRTMUnblockTrace019.rawWord (bumpDigits digits)))
    (PSTRTMRawNat010.rawIncrementTrace digits) (unblockTrace (bumpDigits digits))
  · exact PSTRTMRawNat010.raw_increment_runs digits
  · have h := unblock_runs (bumpDigits digits)
    refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1⟩
    rw [increment_final_tape]
    exact h.1

theorem bump_length_le (digits : List Bool) : (bumpDigits digits).length ≤ digits.length + 1 := by
  induction digits with
  | nil => rfl
  | cons bit later ih => cases bit <;> simp only [bumpDigits, List.length_cons] <;> omega

theorem native_length_le (digits : List Bool) :
    (nativeTrace digits).length ≤ 2 * digits.length ^ 2 + 32 * digits.length + 29 := by
  have hr := PSTRTMRawNat010.raw_increment_length_le digits
  have hb := bump_length_le digits
  have hsq : (bumpDigits digits).length ^ 2 ≤ (digits.length + 1) ^ 2 := Nat.pow_le_pow_left hb 2
  simp only [nativeTrace, List.length_append, List.length_map, unblock_length]
  nlinarith

/-- Complete input/output codec and carry computation. All expansion,
contraction, copying, transfers, rewinds and HALT configurations are included
in nativeTrace; space is ORIGINAL visitedSpace of that same actual trace. -/
theorem native_computes_digits (digits : List Bool) :
    computes nativeIncrementMachine (PSTRTMUnblockTrace019.rawWord digits) (PSTRTMUnblockTrace019.rawWord (bumpDigits digits))
      (512 * (digits.length + 1)^2) (512 * (digits.length + 1)^2) := by
  refine ⟨nativeTrace digits, nativeFinal digits, native_runs digits, ?_, ?_, ?_⟩
  · simp [nativeFinal, PSTRTMSeq005.rightCfg, PSTRTMUnblock018.state, Turing.Tape.mk₂]
  · have ht := native_length_le digits
    nlinarith
  · have hs := PSTRTMTrace002.visitedSpace_le nativeIncrementMachine (PSTRTMUnblockTrace019.rawWord digits).length (nativeTrace digits)
    have ht := native_length_le digits
    simp only [PSTRTMUnblockTrace019.rawWord, List.length_append, List.length_replicate, List.length_cons] at hs ⊢
    nlinarith

/-- EXACT original encoding at BOTH ends. Uniform fixed finite Bool control,
no extra input certificate/preprocessing promise and quadratic actual cost. -/
theorem encodeNat_increment_computes (value : Nat) :
    computes nativeIncrementMachine (encodeNat value) (encodeNat (value + 1))
      (512 * (natBits value + 1)^2) (512 * (natBits value + 1)^2) := by
  have h := native_computes_digits (rawPayload value)
  rw [rawWord_bump] at h
  simpa [PSTRTMUnblockTrace019.rawWord, rawPayload, encodeNat] using h

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeIncrement021
