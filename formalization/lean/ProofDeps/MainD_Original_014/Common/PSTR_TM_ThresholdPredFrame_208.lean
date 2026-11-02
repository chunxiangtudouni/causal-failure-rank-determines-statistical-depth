module
public import Common.PSTR_TM_ThresholdTrimFrame_207
public import Common.PSTR_TM_ThresholdCountdownRun_166

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdPredFrame208
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCountdownCode164

private theorem payload_has_true (value : Nat) (hv : 0 < value) :
    true ∈ PSTRTMNatValue017.rawPayload value := by
  apply has_true_of_value_pos
  simpa only [PSTRTMNatValue017.valueDigits_rawPayload] using hv

theorem pred_payload_value (value : Nat) (hv : 0 < value) :
    PSTRTMIncrement009.valueDigits (predDigits (PSTRTMNatValue017.rawPayload value)) = value - 1 := by
  have h := pred_value (PSTRTMNatValue017.rawPayload value) (payload_has_true value hv)
  rw [PSTRTMNatValue017.valueDigits_rawPayload] at h
  omega

theorem pred_positive (value : Nat) (hv : 1 < value) :
    true ∈ predDigits (PSTRTMNatValue017.rawPayload value) := by
  apply has_true_of_value_pos
  rw [pred_payload_value value (by omega)]
  omega

/-- Same frozen9-label ONE-borrow and17-label trim, with their genuine
retained-tape proofs. This fixed26-label composition is the specific
threshold D-1 call, not a new general subtraction implementation. -/
def predMachine : Machine 25 :=
  PSTRTMSeq005.seqMachine countdownMachine PSTRTMTrimCode103.trimMachine

def predTrace (archive : List Bool) (value : Nat) : List (MachineState 25) :=
  (PSTRTMThresholdCountdownRun166.borrowTrace archive 0 (PSTRTMNatValue017.rawPayload value) []).map
    (PSTRTMSeq005.leftCfg (b := 16)) ++
  (PSTRTMThresholdTrimFrame207.trimTrace archive (predDigits (PSTRTMNatValue017.rawPayload value))).map
    (PSTRTMSeq005.rightCfg (a := 8))

def predFinal (archive : List Bool) (value : Nat) : MachineState 25 :=
  PSTRTMSeq005.rightCfg (a := 8) (PSTRTMTrimCode103.state 14 (false::archive)
    (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (value - 1))))

theorem pred_runsFrom (archive : List Bool) (value : Nat) (hv : 1 < value) :
    PSTRTMSeq005.RunsFrom predMachine
      ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩
      (predTrace archive value) (predFinal archive value) := by
  apply PSTRTMSeq005.seq_runsFrom countdownMachine PSTRTMTrimCode103.trimMachine
    (state 0 (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value)))
    (state 8 (false::archive) (PSTRTMIncrement009.blocks (predDigits (PSTRTMNatValue017.rawPayload value))))
    (PSTRTMTrimCode103.state 14 (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (value - 1))))
    (PSTRTMThresholdCountdownRun166.borrowTrace archive 0 (PSTRTMNatValue017.rawPayload value) [])
    (PSTRTMThresholdTrimFrame207.trimTrace archive (predDigits (PSTRTMNatValue017.rawPayload value)))
  · simpa only [List.append_nil] using
      PSTRTMThresholdCountdownRun166.natural_countdown_runsFrom archive [] value (by omega)
  · have ht := PSTRTMThresholdTrimFrame207.trim_runsFrom archive _ (pred_positive value hv)
    simpa only [PSTRTMThresholdTrimFrame207.trimFinal,PSTRTMTrimValue104.trimmed_canonical,
      pred_payload_value value (by omega),state,PSTRTMTrimCode103.state] using ht

theorem pred_final_tape (archive : List Bool) (value : Nat) :
    (predFinal archive value).Tape = Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (value - 1))) := rfl

theorem pred_length_le (archive : List Bool) (value : Nat) (hv : 1 < value) :
    (predTrace archive value).length ≤ 32*(natBits value + 1) := by
  have hb := PSTRTMThresholdCountdownRun166.borrow_length_le archive 0
    (PSTRTMNatValue017.rawPayload value) [] (payload_has_true value (by omega))
  have ht := PSTRTMThresholdTrimFrame207.trim_length_le archive (predDigits (PSTRTMNatValue017.rawPayload value))
  have hl : (PSTRTMNatValue017.rawPayload value).length = natBits value := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  rw [hl] at hb
  rw [pred_length,hl] at ht
  simp only [predTrace,List.length_append,List.length_map]
  omega

theorem pred_visitedSpace_le (archive : List Bool) (value inputLength : Nat) (hv : 1 < value) :
    visitedSpace predMachine inputLength (predTrace archive value) ≤ inputLength + 64*(natBits value + 1) + 1 := by
  have ht := pred_length_le archive value hv
  have hs := PSTRTMTrace002.visitedSpace_le predMachine inputLength (predTrace archive value)
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdPredFrame208
