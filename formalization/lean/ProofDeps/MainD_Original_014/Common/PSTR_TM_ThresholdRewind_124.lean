module
public import Common.PSTR_TM_ThresholdFields_118
public import Common.PSTR_TM_PairRewind_105

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRewind124
open PaperProofs.Common.Native.RationalControllerComputation

/-- Fixed actual two/four left moves bridge the ORIGINAL00 and0010
field boundaries. No head reset, risk reload or length input is used. -/
def twoMachine : Machine 2 := fun q _ => if h:q.val<2 then
  some (⟨q.val+1,by omega⟩,.move .left) else none

def fourMachine : Machine 4 := fun q _ => if h:q.val<4 then
  some (⟨q.val+1,by omega⟩,.move .left) else none

def twoTrace (tape : Turing.Tape Bool) : List (MachineState 2) :=
  [⟨0,tape⟩,⟨1,tape.move .left⟩,⟨2,(tape.move .left).move .left⟩]

def fourTrace (tape : Turing.Tape Bool) : List (MachineState 4) :=
  [⟨0,tape⟩,⟨1,tape.move .left⟩,⟨2,(tape.move .left).move .left⟩,
    ⟨3,((tape.move .left).move .left).move .left⟩,
    ⟨4,(((tape.move .left).move .left).move .left).move .left⟩]

theorem two_runsFrom (tape : Turing.Tape Bool) :
    PSTRTMSeq005.RunsFrom twoMachine ⟨0,tape⟩ (twoTrace tape) ⟨2,(tape.move .left).move .left⟩ := by
  refine ⟨rfl,?_,rfl,?HE⟩
  · simp [twoTrace,List.isChain_cons_cons,Turing.TM0.step,twoMachine]
  case HE => simp [Turing.TM0.step,twoMachine]

theorem four_runsFrom (tape : Turing.Tape Bool) :
    PSTRTMSeq005.RunsFrom fourMachine ⟨0,tape⟩ (fourTrace tape)
      ⟨4,(((tape.move .left).move .left).move .left).move .left⟩ := by
  refine ⟨rfl,?_,rfl,?HE⟩
  · simp [fourTrace,List.isChain_cons_cons,Turing.TM0.step,fourMachine]
  case HE => simp [Turing.TM0.step,fourMachine]

def denominatorLeft (numerator : List Bool) : List Bool :=
  false::true::false::false::PSTRTMRawNat010.leftBlocks numerator.reverse

def depthLeft (numerator denominator : List Bool) : List Bool :=
  false::false::(PSTRTMRawNat010.leftBlocks denominator.reverse++denominatorLeft numerator)

def sourceWord (numerator denominator depth : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks numerator++[false,false,true,false]++
    PSTRTMIncrement009.blocks denominator++[false,false]++PSTRTMIncrement009.blocks depth

def denominatorTape (numerator denominator depth : List Bool) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (denominatorLeft numerator)
    (PSTRTMIncrement009.blocks denominator++false::false::PSTRTMIncrement009.blocks depth)

def denominatorEOF (numerator denominator depth : List Bool) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (PSTRTMRawNat010.leftBlocks denominator.reverse++denominatorLeft numerator)
    (false::false::PSTRTMIncrement009.blocks depth)

def numeratorEOF (numerator denominator depth : List Bool) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (PSTRTMRawNat010.leftBlocks numerator.reverse)
    (false::false::true::false::(PSTRTMIncrement009.blocks denominator++false::false::PSTRTMIncrement009.blocks depth))

theorem two_final_tape (numerator denominator depth : List Bool) :
    ((Turing.Tape.mk₂ (depthLeft numerator denominator) (PSTRTMIncrement009.blocks depth)).move .left).move .left =
      denominatorEOF numerator denominator depth := by
  simp [depthLeft,denominatorEOF,Turing.Tape.mk₂]

theorem four_final_tape (numerator denominator depth : List Bool) :
    ((((denominatorTape numerator denominator depth).move .left).move .left).move .left).move .left =
      numeratorEOF numerator denominator depth := by
  simp [denominatorTape,denominatorLeft,numeratorEOF,Turing.Tape.mk₂]

def denominatorMachine : Machine 6 := PSTRTMSeq005.seqMachine twoMachine PSTRTMMulRewind085.rewindMachine

def markerMachine : Machine 11 := PSTRTMSeq005.seqMachine denominatorMachine fourMachine

def rewindMachine : Machine 15 := PSTRTMSeq005.seqMachine markerMachine PSTRTMMulRewind085.rewindMachine

def denominatorTrace (numerator denominator depth : List Bool) : List (MachineState 6) :=
  (twoTrace (Turing.Tape.mk₂ (depthLeft numerator denominator) (PSTRTMIncrement009.blocks depth))).map (PSTRTMSeq005.leftCfg (b:=3)) ++
    (PSTRTMPairRewind105.fullTrace (true::false::false::PSTRTMRawNat010.leftBlocks numerator.reverse)
      denominator.reverse (false::false::PSTRTMIncrement009.blocks depth)).map (PSTRTMSeq005.rightCfg (a:=2))

def markerTrace (numerator denominator depth : List Bool) : List (MachineState 11) :=
  (denominatorTrace numerator denominator depth).map (PSTRTMSeq005.leftCfg (b:=4)) ++
    (fourTrace (denominatorTape numerator denominator depth)).map (PSTRTMSeq005.rightCfg (a:=6))

def rewindTrace (numerator denominator depth : List Bool) : List (MachineState 15) :=
  (markerTrace numerator denominator depth).map (PSTRTMSeq005.leftCfg (b:=3)) ++
    (PSTRTMPairRewind105.fullTrace [] numerator.reverse
      (false::false::true::false::(PSTRTMIncrement009.blocks denominator++false::false::PSTRTMIncrement009.blocks depth))).map
        (PSTRTMSeq005.rightCfg (a:=11))

def rewindInitial (numerator denominator depth : List Bool) : MachineState 15 :=
  PSTRTMSeq005.leftCfg (b:=3) (PSTRTMSeq005.leftCfg (b:=4) (PSTRTMSeq005.leftCfg (b:=3)
    (⟨0,Turing.Tape.mk₂ (depthLeft numerator denominator) (PSTRTMIncrement009.blocks depth)⟩ : MachineState 2)))

def rewindFinal (numerator denominator depth : List Bool) : MachineState 15 :=
  PSTRTMSeq005.rightCfg (a:=11) (PSTRTMMulRewind085.state 3 [false] (sourceWord numerator denominator depth))

theorem denominator_runsFrom (numerator denominator depth : List Bool) :
    PSTRTMSeq005.RunsFrom denominatorMachine
      (PSTRTMSeq005.leftCfg (b:=3) (⟨0,Turing.Tape.mk₂ (depthLeft numerator denominator) (PSTRTMIncrement009.blocks depth)⟩ : MachineState 2))
      (denominatorTrace numerator denominator depth)
      (PSTRTMSeq005.rightCfg (a:=2) (PSTRTMMulRewind085.state 3 (denominatorLeft numerator)
        (PSTRTMIncrement009.blocks denominator++false::false::PSTRTMIncrement009.blocks depth))) := by
  apply PSTRTMSeq005.seq_runsFrom twoMachine PSTRTMMulRewind085.rewindMachine _
    ⟨2,denominatorEOF numerator denominator depth⟩ _ _ _
  · simpa only [two_final_tape] using two_runsFrom
      (Turing.Tape.mk₂ (depthLeft numerator denominator) (PSTRTMIncrement009.blocks depth))
  · exact PSTRTMPairRewind105.rewind_runsFrom
      (true::false::false::PSTRTMRawNat010.leftBlocks numerator.reverse) denominator _

theorem marker_runsFrom (numerator denominator depth : List Bool) :
    PSTRTMSeq005.RunsFrom markerMachine
      (PSTRTMSeq005.leftCfg (b:=4) (PSTRTMSeq005.leftCfg (b:=3)
        (⟨0,Turing.Tape.mk₂ (depthLeft numerator denominator) (PSTRTMIncrement009.blocks depth)⟩ : MachineState 2)))
      (markerTrace numerator denominator depth)
      (PSTRTMSeq005.rightCfg (a:=6) (⟨4,numeratorEOF numerator denominator depth⟩ : MachineState 4)) := by
  apply PSTRTMSeq005.seq_runsFrom denominatorMachine fourMachine _ _ _ _ _
    (denominator_runsFrom numerator denominator depth)
  have h := four_runsFrom (denominatorTape numerator denominator depth)
  rw [four_final_tape] at h
  simpa only [denominatorTape,PSTRTMSeq005.rightCfg,PSTRTMMulRewind085.state] using h

theorem rewind_runsFrom (numerator denominator depth : List Bool) :
    PSTRTMSeq005.RunsFrom rewindMachine (rewindInitial numerator denominator depth)
      (rewindTrace numerator denominator depth) (rewindFinal numerator denominator depth) := by
  apply PSTRTMSeq005.seq_runsFrom markerMachine PSTRTMMulRewind085.rewindMachine _ _ _ _ _
    (marker_runsFrom numerator denominator depth)
  have h := PSTRTMPairRewind105.rewind_runsFrom [] numerator
    (false::false::true::false::(PSTRTMIncrement009.blocks denominator++false::false::PSTRTMIncrement009.blocks depth))
  have hz := PSTRTMRawNat010.blank_append_false (PSTRTMRawNat010.leftBlocks numerator.reverse)
  simpa only [PSTRTMSeq005.rightCfg,numeratorEOF,PSTRTMMulRewind085.state,Turing.Tape.mk₂,List.append_nil,hz,
    sourceWord,List.append_assoc,List.cons_append,List.nil_append] using h

theorem rewind_length (numerator denominator depth : List Bool) :
    (rewindTrace numerator denominator depth).length=2*numerator.length+2*denominator.length+14 := by
  simp only [rewindTrace,markerTrace,denominatorTrace,List.length_append,List.length_map,
    twoTrace,fourTrace,List.length_cons,List.length_nil,PSTRTMPairRewind105.full_length,List.length_reverse]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRewind124
