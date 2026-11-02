module
public import Structure.PA17_TM_Division_Codec_003c
public import Common.PSTR_TM_CompactRun_051
public import Common.PSTR_TM_TrimRun_111
public import Common.PSTR_TM_UnblockTrace_019

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
open PaperProofs.Common.Native.RationalControllerComputation

def blocksCodecMachine : Machine 71 :=
  PSTRTMSeq005.seqMachine PSTRTMCompactCode046.compactMachine PSTRTMTrimCode103.trimMachine

/-- One fixed92-label genuine output codec. The input is an internal
result track whose other data track has actually been cleared. All high
zero flags are physically erased, including the canonical-zero branch. -/
def resultCodecMachine : Machine 91 :=
  PSTRTMSeq005.seqMachine blocksCodecMachine PSTRTMUnblock018.unblockMachine

def blocksCodecTrace (digits : List Bool) : List (MachineState 71) :=
  (PSTRTMCompactRun051.compactTrace digits).map (PSTRTMSeq005.leftCfg (b := 16)) ++
    (PSTRTMTrimRun111.trimTrace digits).map (PSTRTMSeq005.rightCfg (a := 54))

def blocksCodecFinal (digits : List Bool) : MachineState 71 :=
  PSTRTMSeq005.rightCfg (a := 54) (PSTRTMTrimRun111.trimFinal digits)

def resultCodecTrace (digits : List Bool) : List (MachineState 91) :=
  (blocksCodecTrace digits).map (PSTRTMSeq005.leftCfg (b := 19)) ++
    (PSTRTMUnblockTrace019.unblockTrace
      (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits digits))).map
      (PSTRTMSeq005.rightCfg (a := 71))

def resultCodecFinal (digits : List Bool) : MachineState 91 :=
  PSTRTMSeq005.rightCfg (a := 71)
    (PSTRTMUnblock018.state 19 [false]
      (PSTRTMUnblockTrace019.rawWord
        (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits digits))))

theorem blocksCodec_runs (digits : List Bool) :
    Runs blocksCodecMachine (PSTRTMBinaryAdd024.resultColumns digits)
      (blocksCodecTrace digits) (blocksCodecFinal digits) := by
  apply PSTRTMSeq005.seq_runs PSTRTMCompactCode046.compactMachine PSTRTMTrimCode103.trimMachine
    (PSTRTMBinaryAdd024.resultColumns digits)
    (PSTRTMCompactCode046.state 54 [false] (PSTRTMIncrement009.blocks digits ++ [false,false]))
    (PSTRTMTrimRun111.trimFinal digits)
    (PSTRTMCompactRun051.compactTrace digits) (PSTRTMTrimRun111.trimTrace digits)
    (PSTRTMCompactRun051.compact_runs digits)
  have hr := PSTRTMTrimRun111.trim_runs digits
  rw [PSTRTMCompactRun051.compact_final_tape]
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

theorem blocksCodec_final_tape (digits : List Bool) :
    (blocksCodecFinal digits).Tape =
      Turing.Tape.mk₁ (PSTRTMIncrement009.blocks
        (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits digits))) :=
  PSTRTMTrimRun111.trim_final_tape digits

theorem resultCodec_runs (digits : List Bool) :
    Runs resultCodecMachine (PSTRTMBinaryAdd024.resultColumns digits)
      (resultCodecTrace digits) (resultCodecFinal digits) := by
  apply PSTRTMSeq005.seq_runs blocksCodecMachine PSTRTMUnblock018.unblockMachine
    (PSTRTMBinaryAdd024.resultColumns digits) (blocksCodecFinal digits)
    (PSTRTMUnblock018.state 19 [false]
      (PSTRTMUnblockTrace019.rawWord
        (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits digits))))
    (blocksCodecTrace digits)
    (PSTRTMUnblockTrace019.unblockTrace
      (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits digits)))
    (blocksCodec_runs digits)
  have hr := PSTRTMUnblockTrace019.unblock_runs
    (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits digits))
  rw [blocksCodec_final_tape]
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

theorem resultCodec_final_tape (digits : List Bool) :
    (resultCodecFinal digits).Tape = Turing.Tape.mk₁ (encodeNat (PSTRTMIncrement009.valueDigits digits)) := by
  have he : PSTRTMUnblockTrace019.rawWord
      (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits digits)) =
      encodeNat (PSTRTMIncrement009.valueDigits digits) := by
    simp [PSTRTMUnblockTrace019.rawWord, PSTRTMNatValue017.rawPayload, encodeNat]
  simp only [resultCodecFinal, PSTRTMSeq005.rightCfg, PSTRTMUnblock018.state,
    Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false, he]

theorem resultCodec_payload_length_le (digits : List Bool) :
    (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits digits)).length ≤
      digits.length + 1 := by
  have h := PSTRTMTrimValue104.trimmed_length_le digits
  rw [PSTRTMTrimValue104.trimmed_canonical] at h
  exact h

theorem resultCodecTrace_length_le (digits : List Bool) :
    (resultCodecTrace digits).length ≤ 128 * (digits.length + 1)^2 := by
  have ht := PSTRTMTrimRun111.trim_length_le digits
  have hp := resultCodec_payload_length_le digits
  have hp2 := Nat.pow_le_pow_left hp 2
  simp only [resultCodecTrace, blocksCodecTrace, List.length_append, List.length_map,
    PSTRTMCompactRun051.compact_length, PSTRTMUnblockTrace019.unblock_length]
  nlinarith

theorem resultCodecTrace_visitedSpace_le (digits : List Bool) :
    visitedSpace resultCodecMachine (PSTRTMBinaryAdd024.resultColumns digits).length
      (resultCodecTrace digits) ≤ 512 * (digits.length + 1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le resultCodecMachine
    (PSTRTMBinaryAdd024.resultColumns digits).length (resultCodecTrace digits)
  have ht := resultCodecTrace_length_le digits
  rw [PSTRTMCompactRun051.resultColumns_length] at hs ⊢
  nlinarith

/-- Internal exact result transport, valid for arbitrary padded digits,
including empty and all false lists. This is not an original division
theorem: the shared loop must actually produce and isolate its result. -/
theorem resultCodec_computes (digits : List Bool) :
    computes resultCodecMachine (PSTRTMBinaryAdd024.resultColumns digits)
      (encodeNat (PSTRTMIncrement009.valueDigits digits))
      (128 * (digits.length + 1)^2) (512 * (digits.length + 1)^2) := by
  refine ⟨resultCodecTrace digits, resultCodecFinal digits, resultCodec_runs digits,
    ?_, resultCodecTrace_length_le digits, resultCodecTrace_visitedSpace_le digits⟩
  rw [resultCodec_final_tape]
  simp [Turing.Tape.mk₁, Turing.Tape.mk₂]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
