module
public import Common.PSTR_TM_ThresholdRewind_124

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdSource125
open PaperProofs.Common.Native.RationalControllerComputation

def first (risk : Rat) := PSTRTMThresholdRisk114.first risk
def second (risk : Rat) := PSTRTMThresholdRisk114.second risk
def depthDigits (depth : Nat) := PSTRTMNatValue017.rawPayload depth

/-- ORIGINAL threshold input to the actual numerator cursor, with all
three decoded fields retained. This is an actual source for the right
workspace copier, not an assumed pointer or a change of input format. -/
def sourceMachine : Machine 182 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdFields118.fieldsMachine PSTRTMThresholdRewind124.rewindMachine

def sourceTrace (risk : Rat) (depth : Nat) : List (MachineState 182) :=
  (PSTRTMThresholdFields118.fieldsTrace risk depth).map (PSTRTMSeq005.leftCfg (b:=15)) ++
    (PSTRTMThresholdRewind124.rewindTrace (first risk) (second risk) (depthDigits depth)).map (PSTRTMSeq005.rightCfg (a:=166))

def sourceFinal (risk : Rat) (depth : Nat) : MachineState 182 :=
  PSTRTMSeq005.rightCfg (a:=166) (PSTRTMThresholdRewind124.rewindFinal (first risk) (second risk) (depthDigits depth))

theorem source_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    Runs sourceMachine (encode [.rational risk,.natural depth]) (sourceTrace risk depth) (sourceFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs PSTRTMThresholdFields118.fieldsMachine PSTRTMThresholdRewind124.rewindMachine
    (encode [.rational risk,.natural depth]) (PSTRTMThresholdFields118.fieldsFinal risk depth)
    (PSTRTMThresholdRewind124.rewindFinal (first risk) (second risk) (depthDigits depth))
    (PSTRTMThresholdFields118.fieldsTrace risk depth)
    (PSTRTMThresholdRewind124.rewindTrace (first risk) (second risk) (depthDigits depth))
    (PSTRTMThresholdFields118.fields_runs risk depth hr)
  have h := PSTRTMThresholdRewind124.rewind_runsFrom (first risk) (second risk) (depthDigits depth)
  rw [PSTRTMThresholdFields118.fields_final_tape]
  simpa only [PSTRTMThresholdRewind124.rewindInitial,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,
    PSTRTMThresholdRewind124.depthLeft,PSTRTMThresholdRewind124.denominatorLeft,
    PSTRTMThresholdFields118.depthContext,PSTRTMThresholdFields118.numeratorLeft,first,second,depthDigits,Fin.val_zero,Fin.mk_zero] using h

theorem source_final_tape (risk : Rat) (depth : Nat) : (sourceFinal risk depth).Tape =
    Turing.Tape.mk₁ (PSTRTMThresholdRewind124.sourceWord (first risk) (second risk) (depthDigits depth)) := by
  simp only [sourceFinal,PSTRTMSeq005.rightCfg,PSTRTMThresholdRewind124.rewindFinal,
    PSTRTMMulRewind085.state,Turing.Tape.mk₂,Turing.Tape.mk₁,PSTRTMRawNat010.blank_single_false]

private theorem arithmetic_bound (parse n m input : Nat)
    (hp : parse ≤ 2048*(input+1)^2) (hw : n+m ≤ input+1) :
    parse+(2*n+2*m+14) ≤ 4096*(input+1)^2 := by nlinarith

theorem source_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    (sourceTrace risk depth).length ≤ 4096*((encode [.rational risk,.natural depth]).length+1)^2 := by
  have hp := PSTRTMThresholdFields118.fields_length_le risk depth hr
  have hw := PSTRTMThresholdRisk114.original_widths_le risk depth hr
  simp only [sourceTrace,List.length_append,List.length_map,PSTRTMThresholdRewind124.rewind_length,
    first,second,PSTRTMThresholdRisk114.first_length,PSTRTMThresholdRisk114.second_length]
  exact arithmetic_bound _ _ _ _ hp hw

private theorem arithmetic_space (input time space : Nat)
    (ht : time ≤ 4096*(input+1)^2) (hs : space ≤ input+2*time+1) : space ≤ 16384*(input+1)^2 := by nlinarith

theorem source_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    visitedSpace sourceMachine (encode [.rational risk,.natural depth]).length (sourceTrace risk depth) ≤
      16384*((encode [.rational risk,.natural depth]).length+1)^2 :=
  arithmetic_space _ _ _ (source_length_le risk depth hr)
    (PSTRTMTrace002.visitedSpace_le sourceMachine (encode [.rational risk,.natural depth]).length (sourceTrace risk depth))

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdSource125
