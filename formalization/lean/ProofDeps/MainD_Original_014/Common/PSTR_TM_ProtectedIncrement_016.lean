module
public import Common.PSTR_TM_FullRawPadding_015
public import Common.PSTR_TM_IncrementFrame_013

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMProtectedIncrement016
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPaddedNat012 PSTRTMFullRawPadding015 PSTRTMIncrement009 PSTRTMIncrementFrame013

/-- One fixed Bool machine: construct the actual00 isolation zone from the
original raw field, then invoke the verified carry machine on that tape. -/
def protectedIncrementMachine : Machine 121 :=
  PSTRTMSeq005.seqMachine paddedNatMachine incrementMachine

def protectedTrace (digits suffix : List Bool) : List (MachineState 121) :=
  (paddedTrace [] digits suffix).map (PSTRTMSeq005.leftCfg (b := 14)) ++
    (frameTrace 0 digits (true :: false :: suffix)).map (PSTRTMSeq005.rightCfg (a := 106))

def protectedFinal (digits suffix : List Bool) : MachineState 121 :=
  PSTRTMSeq005.rightCfg (a := 106)
    (PSTRTMIncrement009.state 14 [false]
      (blocks (bumpDigits digits) ++ remainingPad digits ++ true :: false :: suffix))

theorem protected_runs (digits suffix : List Bool) :
    Runs protectedIncrementMachine
      (List.replicate digits.length true ++ false :: (digits ++ suffix))
      (protectedTrace digits suffix) (protectedFinal digits suffix) := by
  apply PSTRTMSeq005.seq_runs paddedNatMachine incrementMachine
    (List.replicate digits.length true ++ false :: (digits ++ suffix))
    (PSTRTMPaddedNat012.state (post suffix.headI 44) [false]
      (blocks digits ++ false :: false :: true :: false :: suffix))
    (PSTRTMIncrement009.state 14 [false]
      (blocks (bumpDigits digits) ++ remainingPad digits ++ true :: false :: suffix))
    (paddedTrace [] digits suffix) (frameTrace 0 digits (true :: false :: suffix))
  · exact padded_runs digits suffix
  · have h := increment_frame_runs digits (true :: false :: suffix)
    refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1⟩
    rw [padded_final_tape]
    exact h.1

theorem protected_length_le (digits suffix : List Bool) :
    (protectedTrace digits suffix).length ≤ digits.length ^ 2 + 33 * digits.length + 36 := by
  have h := frameTrace_length_le 0 digits (true :: false :: suffix)
  simp only [protectedTrace, List.length_append, List.length_map, padded_length, List.length_nil]
  nlinarith

/-- Arbitrary suffixes require no input padding promise. The fixed program
actually constructs, pays for and consumes the protected region. Its output
is still the explicit internal flagged-cell encoding. -/
theorem protected_computes (digits suffix : List Bool) :
    computes protectedIncrementMachine
      (List.replicate digits.length true ++ false :: (digits ++ suffix))
      (blocks (bumpDigits digits) ++ remainingPad digits ++ true :: false :: suffix)
      (1024 * (digits.length + 1) ^ 2) (1024 * (digits.length + 1) ^ 2 + suffix.length) := by
  refine ⟨protectedTrace digits suffix, protectedFinal digits suffix, protected_runs digits suffix, ?_, ?_, ?_⟩
  · simp [protectedFinal, PSTRTMSeq005.rightCfg, PSTRTMIncrement009.state, Turing.Tape.mk₂]
  · have h := protected_length_le digits suffix
    nlinarith
  · have hs := PSTRTMTrace002.visitedSpace_le protectedIncrementMachine
      (List.replicate digits.length true ++ false :: (digits ++ suffix)).length (protectedTrace digits suffix)
    have ht := protected_length_le digits suffix
    simp only [List.length_append, List.length_replicate, List.length_cons] at hs ⊢
    nlinarith

/-- Original B23 raw Nat encoding, with every additional raw suffix bit.
There is no pre-expanded block or pre-allocated isolation zone in the input. -/
theorem encodeNat_protected_increment_computes (value : Nat) (suffix : List Bool) :
    let payload := List.ofFn (fun i : Fin (natBits value) => value.testBit i.val)
    computes protectedIncrementMachine (encodeNat value ++ suffix)
      (blocks (bumpDigits payload) ++ remainingPad payload ++ true :: false :: suffix)
      (1024 * (natBits value + 1) ^ 2) (1024 * (natBits value + 1) ^ 2 + suffix.length) := by
  dsimp only
  have h := protected_computes (List.ofFn (fun i : Fin (natBits value) => value.testBit i.val)) suffix
  simpa [encodeNat, List.append_assoc] using h

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMProtectedIncrement016
