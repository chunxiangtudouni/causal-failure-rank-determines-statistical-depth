module
public import Common.PSTR_TM_PackFrameCost_150

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdPairRewind151
open PaperProofs.Common.Native.RationalControllerComputation

/-- Original risk/depth data behind the REAL false guard of the NUM copy.
The list is real retained tape obtained from142, not a new caller oracle. -/
def workArchive (archive numerator denominator depth : List Bool) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks depth.reverse++false::true::false::false::
    (PSTRTMRawNat010.leftBlocks denominator.reverse++false::PSTRTMThresholdDenPrepare141.denArchive archive numerator))

def tail (denominator : List Bool) : List Bool :=
  [false,false,true,false]++PSTRTMIncrement009.blocks denominator

def firstFinal (archive numerator denominator depth : List Bool) : MachineState 4 :=
  let tape := (PSTRTMThresholdDenBackup142.denBackupFinal archive numerator denominator depth).Tape
  ⟨4,(((tape.move .left).move .left).move .left).move .left⟩

theorem four_final_tape (archive numerator denominator depth : List Bool) :
    (firstFinal archive numerator denominator depth).Tape=Turing.Tape.mk₂
      (PSTRTMRawNat010.leftBlocks numerator.reverse++false::workArchive archive numerator denominator depth)
      (tail denominator) := by
  unfold firstFinal
  rw [PSTRTMThresholdDenBackup142.denBackup_final_tape]
  simp [workArchive,tail,Turing.Tape.mk₂]

/-- SAME fixed five-label four-left transport and four-label pair rewind.
The head actually crosses the new0010 and every NUM-copy flag, returning
to the first working NUM digit. No archive reload or free reset occurs. -/
def rewindMachine : Machine 8 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdRewind124.fourMachine PSTRTMMulRewind085.rewindMachine

def rewindTrace (archive numerator denominator depth : List Bool) : List (MachineState 8) :=
  (PSTRTMThresholdRewind124.fourTrace
    (PSTRTMThresholdDenBackup142.denBackupFinal archive numerator denominator depth).Tape).map
      (PSTRTMSeq005.leftCfg (b:=3)) ++
  (PSTRTMPairRewind105.fullTrace (workArchive archive numerator denominator depth) numerator.reverse
    (tail denominator)).map (PSTRTMSeq005.rightCfg (a:=4))

def rewindFinal (archive numerator denominator depth : List Bool) : MachineState 8 :=
  PSTRTMSeq005.rightCfg (a:=4) (PSTRTMMulRewind085.state 3
    (false::workArchive archive numerator denominator depth)
    (PSTRTMIncrement009.blocks numerator++tail denominator))

theorem rewind_runsFrom (archive numerator denominator depth : List Bool) :
    PSTRTMSeq005.RunsFrom rewindMachine
      ⟨0,(PSTRTMThresholdDenBackup142.denBackupFinal archive numerator denominator depth).Tape⟩
      (rewindTrace archive numerator denominator depth) (rewindFinal archive numerator denominator depth) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMThresholdRewind124.fourMachine PSTRTMMulRewind085.rewindMachine
    ⟨0,(PSTRTMThresholdDenBackup142.denBackupFinal archive numerator denominator depth).Tape⟩
    (firstFinal archive numerator denominator depth)
    (PSTRTMMulRewind085.state 3 (false::workArchive archive numerator denominator depth)
      (PSTRTMIncrement009.blocks numerator++tail denominator))
    (PSTRTMThresholdRewind124.fourTrace
      (PSTRTMThresholdDenBackup142.denBackupFinal archive numerator denominator depth).Tape)
    (PSTRTMPairRewind105.fullTrace (workArchive archive numerator denominator depth) numerator.reverse
      (tail denominator))
    (PSTRTMThresholdRewind124.four_runsFrom _)
  rw [four_final_tape]
  exact PSTRTMPairRewind105.rewind_runsFrom _ _ _

theorem rewind_final_tape (archive numerator denominator depth : List Bool) :
    (rewindFinal archive numerator denominator depth).Tape=Turing.Tape.mk₂
      (false::workArchive archive numerator denominator depth)
      (PSTRTMIncrement009.blocks numerator++[false,false,true,false]++PSTRTMIncrement009.blocks denominator) := by
  simp only [rewindFinal,PSTRTMSeq005.rightCfg,PSTRTMMulRewind085.state,tail,List.append_assoc]

theorem rewind_length (archive numerator denominator depth : List Bool) :
    (rewindTrace archive numerator denominator depth).length=2*numerator.length+8 := by
  simp only [rewindTrace,List.length_append,List.length_map,PSTRTMThresholdRewind124.fourTrace,
    List.length_cons,List.length_nil,PSTRTMPairRewind105.full_length,List.length_reverse]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdPairRewind151
