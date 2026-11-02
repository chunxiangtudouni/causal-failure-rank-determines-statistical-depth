module
public import Common.PSTR_TM_ThresholdMarkerRotate_140

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenPrepare141
open PaperProofs.Common.Native.RationalControllerComputation

def twoLeftMachine : Machine 2 := PSTRTMThresholdRewind124.twoMachine

def state (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩

def twoLeftTrace (first second : Bool) (left right : List Bool) : List (MachineState 2) :=
  [state 0 (first::second::left) right,state 1 (second::left) (first::right),state 2 left (second::first::right)]

theorem twoLeft_runsFrom (first second : Bool) (left right : List Bool) :
    PSTRTMSeq005.RunsFrom twoLeftMachine (state 0 (first::second::left) right)
      (twoLeftTrace first second left right) (state 2 left (second::first::right)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [twoLeftTrace,List.isChain_cons_cons,Turing.TM0.step,twoLeftMachine,PSTRTMThresholdRewind124.twoMachine,state,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,twoLeftMachine,PSTRTMThresholdRewind124.twoMachine,state]

/-- Actual NUM/DEN prefix stored to the left of the DEN guard. These
are retained cells, not a new numeric/performance field in the input. -/
def denArchive (archive numerator : List Bool) : List Bool :=
  true::false::false::(PSTRTMRawNat010.leftBlocks numerator.reverse++false::archive)

def denEndLeft (archive numerator denominator : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks denominator.reverse++false::denArchive archive numerator

def depthArchive (archive numerator denominator : List Bool) : List Bool :=
  false::denEndLeft archive numerator denominator

def markerMachine : Machine 32 := PSTRTMSeq005.seqMachine twoLeftMachine
  PSTRTMThresholdMarkerRotate140.rotateMachine

def markerTrace (archive numerator denominator depth : List Bool) : List (MachineState 32) :=
  (twoLeftTrace false true (false::false::(PSTRTMRawNat010.leftBlocks depth.reverse++
      false::depthArchive archive numerator denominator)) (PSTRTMIncrement009.blocks numerator)).map
    (PSTRTMSeq005.leftCfg (b:=29)) ++
  (PSTRTMThresholdMarkerRotate140.rotateTrace (depthArchive archive numerator denominator) depth
    (PSTRTMIncrement009.blocks numerator)).map (PSTRTMSeq005.rightCfg (a:=2))

def markerInitial (archive numerator denominator depth : List Bool) : MachineState 32 :=
  PSTRTMSeq005.leftCfg (b:=29) (state 0
    (false::true::false::false::(PSTRTMRawNat010.leftBlocks depth.reverse++false::depthArchive archive numerator denominator))
    (PSTRTMIncrement009.blocks numerator))

def markerFinal (archive numerator denominator depth : List Bool) : MachineState 32 :=
  PSTRTMSeq005.rightCfg (a:=2) (PSTRTMThresholdMarkerRotate140.final
    (depthArchive archive numerator denominator) depth (PSTRTMIncrement009.blocks numerator))

theorem marker_runsFrom (archive numerator denominator depth : List Bool) :
    PSTRTMSeq005.RunsFrom markerMachine (markerInitial archive numerator denominator depth)
      (markerTrace archive numerator denominator depth) (markerFinal archive numerator denominator depth) := by
  apply PSTRTMSeq005.seq_runsFrom twoLeftMachine PSTRTMThresholdMarkerRotate140.rotateMachine
    (state 0 (false::true::false::false::(PSTRTMRawNat010.leftBlocks depth.reverse++false::depthArchive archive numerator denominator))
      (PSTRTMIncrement009.blocks numerator))
    (state 2 (false::false::(PSTRTMRawNat010.leftBlocks depth.reverse++false::depthArchive archive numerator denominator))
      (true::false::PSTRTMIncrement009.blocks numerator))
    (PSTRTMThresholdMarkerRotate140.final (depthArchive archive numerator denominator) depth (PSTRTMIncrement009.blocks numerator))
    _ _ (twoLeft_runsFrom _ _ _ _)
  exact PSTRTMThresholdMarkerRotate140.rotate_runsFrom _ _ _

def newTail (numerator depth : List Bool) : List Bool :=
  false::false::true::false::(PSTRTMIncrement009.blocks depth++false::false::PSTRTMIncrement009.blocks numerator)

def rewindMachine : Machine 6 := PSTRTMSeq005.seqMachine twoLeftMachine PSTRTMMulRewind085.rewindMachine

def rewindTrace (archive numerator denominator depth : List Bool) : List (MachineState 6) :=
  (twoLeftTrace false false (denEndLeft archive numerator denominator)
    (true::false::(PSTRTMIncrement009.blocks depth++false::false::PSTRTMIncrement009.blocks numerator))).map
      (PSTRTMSeq005.leftCfg (b:=3)) ++
  (PSTRTMPairRewind105.fullTrace (denArchive archive numerator) denominator.reverse (newTail numerator depth)).map
    (PSTRTMSeq005.rightCfg (a:=2))

def rewindInitial (archive numerator denominator depth : List Bool) : MachineState 6 :=
  PSTRTMSeq005.leftCfg (b:=3) (state 0 (false::false::denEndLeft archive numerator denominator)
    (true::false::(PSTRTMIncrement009.blocks depth++false::false::PSTRTMIncrement009.blocks numerator)))

def rewindFinal (archive numerator denominator depth : List Bool) : MachineState 6 :=
  PSTRTMSeq005.rightCfg (a:=2) (PSTRTMMulRewind085.state 3 (false::denArchive archive numerator)
    (PSTRTMIncrement009.blocks denominator++newTail numerator depth))

theorem rewind_runsFrom (archive numerator denominator depth : List Bool) :
    PSTRTMSeq005.RunsFrom rewindMachine (rewindInitial archive numerator denominator depth)
      (rewindTrace archive numerator denominator depth) (rewindFinal archive numerator denominator depth) := by
  apply PSTRTMSeq005.seq_runsFrom twoLeftMachine PSTRTMMulRewind085.rewindMachine
    (state 0 (false::false::denEndLeft archive numerator denominator)
      (true::false::(PSTRTMIncrement009.blocks depth++false::false::PSTRTMIncrement009.blocks numerator)))
    (state 2 (denEndLeft archive numerator denominator) (newTail numerator depth))
    (PSTRTMMulRewind085.state 3 (false::denArchive archive numerator)
      (PSTRTMIncrement009.blocks denominator++newTail numerator depth))
    _ _ (twoLeft_runsFrom _ _ _ _)
  exact PSTRTMPairRewind105.rewind_runsFrom _ _ _

/-- Fixed40-label actual transport from the NUM-backup head to DEN's
first data cell. The real10 marker is shifted over DEPTH, then the real
DEN flag/guard rewind is run. No field or head is reset for free. -/
def prepareMachine : Machine 39 := PSTRTMSeq005.seqMachine markerMachine rewindMachine

def prepareTrace (archive numerator denominator depth : List Bool) : List (MachineState 39) :=
  (markerTrace archive numerator denominator depth).map (PSTRTMSeq005.leftCfg (b:=6)) ++
    (rewindTrace archive numerator denominator depth).map (PSTRTMSeq005.rightCfg (a:=32))

def prepareInitial (archive numerator denominator depth : List Bool) : MachineState 39 :=
  PSTRTMSeq005.leftCfg (b:=6) (markerInitial archive numerator denominator depth)

def prepareFinal (archive numerator denominator depth : List Bool) : MachineState 39 :=
  PSTRTMSeq005.rightCfg (a:=32) (rewindFinal archive numerator denominator depth)

theorem prepare_runsFrom (archive numerator denominator depth : List Bool) :
    PSTRTMSeq005.RunsFrom prepareMachine (prepareInitial archive numerator denominator depth)
      (prepareTrace archive numerator denominator depth) (prepareFinal archive numerator denominator depth) := by
  apply PSTRTMSeq005.seq_runsFrom markerMachine rewindMachine
    (markerInitial archive numerator denominator depth) (markerFinal archive numerator denominator depth)
    (rewindFinal archive numerator denominator depth)
    (markerTrace archive numerator denominator depth) (rewindTrace archive numerator denominator depth)
    (marker_runsFrom _ _ _ _)
  exact rewind_runsFrom _ _ _ _

theorem prepare_initial_tape (archive numerator denominator depth : List Bool) :
    (prepareInitial archive numerator denominator depth).Tape=
      (PSTRTMThresholdCopyLoop137.copyFinal archive numerator denominator depth).Tape := rfl

/-- The whole final tape is exactly the real126 source layout with DEN
now first. NUM's original field and its copied value are both still real
tape cells; the next copy invocation may read only this actual layout. -/
theorem prepare_final_tape (archive numerator denominator depth : List Bool) :
    (prepareFinal archive numerator denominator depth).Tape=
      (PSTRTMThresholdCopyLoop137.copyInitial (denArchive archive numerator) denominator depth numerator).Tape := by
  simp only [prepareFinal,rewindFinal,PSTRTMSeq005.rightCfg,PSTRTMMulRewind085.state,
    PSTRTMThresholdCopyLoop137.copyInitial,PSTRTMThresholdCopyCode126.state,
    PSTRTMThresholdRewind124.sourceWord,newTail,List.append_assoc,List.cons_append,List.nil_append]

theorem prepare_length (archive numerator denominator depth : List Bool) :
    (prepareTrace archive numerator denominator depth).length=12*depth.length+2*denominator.length+16 := by
  simp only [prepareTrace,markerTrace,rewindTrace,List.length_append,List.length_map,twoLeftTrace,
    List.length_cons,List.length_nil,PSTRTMThresholdMarkerRotate140.rotate_length,
    PSTRTMPairRewind105.full_length,List.length_reverse]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenPrepare141
