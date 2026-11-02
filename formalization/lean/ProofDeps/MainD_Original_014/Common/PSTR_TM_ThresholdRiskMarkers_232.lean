module
public import Common.PSTR_TM_ThresholdRiskLocator_231

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRiskMarkers232
open PaperProofs.Common.Native.RationalControllerComputation

/-! Exact retained-risk0010 marker transport. The existing124 four-left
program and105 rewind are executed, with arbitrary literal archive/suffix.
Both calls leave all digit flags and old markers in place. No parser
silently reads the original DEN-ending01 as an isolated blank00. -/

def markerLeft (archive digits : List Bool) : List Bool :=
  false::true::false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)

def markerTail (suffix : List Bool) : List Bool := false::false::true::false::suffix

def markerMachine : Machine 8 :=
  PSTRTMSeq005.seqMachine PSTRTMThresholdRewind124.fourMachine PSTRTMMulRewind085.rewindMachine

def markerTrace (archive digits suffix : List Bool) : List (MachineState 8) :=
  (PSTRTMThresholdRewind124.fourTrace (Turing.Tape.mk₂ (markerLeft archive digits) suffix)).map
    (PSTRTMSeq005.leftCfg (b := 3)) ++
    (PSTRTMPairRewind105.fullTrace archive digits.reverse (markerTail suffix)).map
      (PSTRTMSeq005.rightCfg (a := 4))

def markerFinal (archive digits suffix : List Bool) : MachineState 8 :=
  PSTRTMSeq005.rightCfg (a := 4) (PSTRTMMulRewind085.state 3 (false::archive)
    (PSTRTMIncrement009.blocks digits++markerTail suffix))

theorem marker_runsFrom (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom markerMachine ⟨0,Turing.Tape.mk₂ (markerLeft archive digits) suffix⟩
      (markerTrace archive digits suffix) (markerFinal archive digits suffix) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMThresholdRewind124.fourMachine PSTRTMMulRewind085.rewindMachine
    ⟨0,Turing.Tape.mk₂ (markerLeft archive digits) suffix⟩
    ⟨4,((((Turing.Tape.mk₂ (markerLeft archive digits) suffix).move .left).move .left).move .left).move .left⟩
    (PSTRTMMulRewind085.state 3 (false::archive) (PSTRTMIncrement009.blocks digits++markerTail suffix))
    (PSTRTMThresholdRewind124.fourTrace (Turing.Tape.mk₂ (markerLeft archive digits) suffix))
    (PSTRTMPairRewind105.fullTrace archive digits.reverse (markerTail suffix))
    (PSTRTMThresholdRewind124.four_runsFrom _)
  have ht : ((((Turing.Tape.mk₂ (markerLeft archive digits) suffix).move .left).move .left).move .left).move .left =
      Turing.Tape.mk₂ (PSTRTMRawNat010.leftBlocks digits.reverse++false::archive) (markerTail suffix) := by
    simp [markerLeft,markerTail,Turing.Tape.mk₂]
  rw [ht]
  exact PSTRTMPairRewind105.rewind_runsFrom _ _ _

theorem marker_final_tape (archive digits suffix : List Bool) :
    (markerFinal archive digits suffix).Tape = Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks digits++markerTail suffix) := rfl

theorem marker_length (archive digits suffix : List Bool) :
    (markerTrace archive digits suffix).length = 2*digits.length+8 := by
  simp only [markerTrace,List.length_append,List.length_map,PSTRTMThresholdRewind124.fourTrace,
    List.length_cons,List.length_nil,PSTRTMPairRewind105.full_length,List.length_reverse]
  omega

def riskFieldsMachine : Machine 17 := PSTRTMSeq005.seqMachine markerMachine markerMachine

def riskFieldsTrace (archive numerator denominator suffix : List Bool) : List (MachineState 17) :=
  (markerTrace (PSTRTMThresholdDenPrepare141.denArchive archive numerator) denominator suffix).map
    (PSTRTMSeq005.leftCfg (b := 8)) ++
    (markerTrace archive numerator (PSTRTMIncrement009.blocks denominator++markerTail suffix)).map
      (PSTRTMSeq005.rightCfg (a := 8))

def riskFieldsFinal (archive numerator denominator suffix : List Bool) : MachineState 17 :=
  PSTRTMSeq005.rightCfg (a := 8)
    (markerFinal archive numerator (PSTRTMIncrement009.blocks denominator++markerTail suffix))

theorem riskFields_runsFrom (archive numerator denominator suffix : List Bool) :
    PSTRTMSeq005.RunsFrom riskFieldsMachine
      ⟨0,Turing.Tape.mk₂ (markerLeft (PSTRTMThresholdDenPrepare141.denArchive archive numerator) denominator) suffix⟩
      (riskFieldsTrace archive numerator denominator suffix) (riskFieldsFinal archive numerator denominator suffix) := by
  apply PSTRTMSeq005.seq_runsFrom markerMachine markerMachine
    ⟨0,Turing.Tape.mk₂ (markerLeft (PSTRTMThresholdDenPrepare141.denArchive archive numerator) denominator) suffix⟩
    (markerFinal (PSTRTMThresholdDenPrepare141.denArchive archive numerator) denominator suffix)
    (markerFinal archive numerator (PSTRTMIncrement009.blocks denominator++markerTail suffix))
    (markerTrace (PSTRTMThresholdDenPrepare141.denArchive archive numerator) denominator suffix)
    (markerTrace archive numerator (PSTRTMIncrement009.blocks denominator++markerTail suffix))
    (marker_runsFrom _ _ _)
  rw [marker_final_tape]
  exact marker_runsFrom _ _ _

theorem riskFields_final_tape (archive numerator denominator suffix : List Bool) :
    (riskFieldsFinal archive numerator denominator suffix).Tape = Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks numerator++markerTail (PSTRTMIncrement009.blocks denominator++markerTail suffix)) := rfl

theorem riskFields_length (archive numerator denominator suffix : List Bool) :
    (riskFieldsTrace archive numerator denominator suffix).length =
      2*(numerator.length+denominator.length)+16 := by
  simp only [riskFieldsTrace,List.length_append,List.length_map,marker_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRiskMarkers232
