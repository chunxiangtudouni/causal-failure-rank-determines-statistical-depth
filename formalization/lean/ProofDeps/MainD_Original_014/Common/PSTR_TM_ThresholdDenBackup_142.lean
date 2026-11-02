module
public import Common.PSTR_TM_ThresholdDenPrepare_141

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenBackup142
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDenPrepare141

/-- Reuse the SAME131-label copier on the physically rearranged
DEN,0010,DEPTH,00,NUMcopy layout. The original fields are retained; a
second real copy is appended on actual blanks. This is not a promise
about an arbitrary right suffix or an externally supplied workzone. -/
def denBackupMachine : Machine 170 := PSTRTMSeq005.seqMachine prepareMachine
  PSTRTMThresholdCopyCode126.copyMachine

def denBackupTrace (archive numerator denominator depth : List Bool) : List (MachineState 170) :=
  (prepareTrace archive numerator denominator depth).map (PSTRTMSeq005.leftCfg (b:=130)) ++
    (PSTRTMThresholdCopyLoop137.copyTrace (denArchive archive numerator) denominator depth numerator).map
      (PSTRTMSeq005.rightCfg (a:=39))

def denBackupFinal (archive numerator denominator depth : List Bool) : MachineState 170 :=
  PSTRTMSeq005.rightCfg (a:=39)
    (PSTRTMThresholdCopyLoop137.copyFinal (denArchive archive numerator) denominator depth numerator)

theorem denBackup_runsFrom (archive numerator denominator depth : List Bool) :
    PSTRTMSeq005.RunsFrom denBackupMachine
      ⟨0,(PSTRTMThresholdCopyLoop137.copyFinal archive numerator denominator depth).Tape⟩
      (denBackupTrace archive numerator denominator depth) (denBackupFinal archive numerator denominator depth) := by
  apply PSTRTMSeq005.seq_runsFrom prepareMachine PSTRTMThresholdCopyCode126.copyMachine
    (prepareInitial archive numerator denominator depth) (prepareFinal archive numerator denominator depth)
    (PSTRTMThresholdCopyLoop137.copyFinal (denArchive archive numerator) denominator depth numerator)
    (prepareTrace archive numerator denominator depth)
    (PSTRTMThresholdCopyLoop137.copyTrace (denArchive archive numerator) denominator depth numerator)
    (prepare_runsFrom _ _ _ _)
  rw [prepare_final_tape]
  exact PSTRTMThresholdCopyLoop137.copy_runsFrom _ _ _ _

theorem denBackup_final_tape (archive numerator denominator depth : List Bool) :
    (denBackupFinal archive numerator denominator depth).Tape=Turing.Tape.mk₂
      (false::true::false::false::(PSTRTMRawNat010.leftBlocks numerator.reverse++false::false::
        (PSTRTMRawNat010.leftBlocks depth.reverse++false::true::false::false::
          (PSTRTMRawNat010.leftBlocks denominator.reverse++false::denArchive archive numerator))))
      (PSTRTMIncrement009.blocks denominator) := PSTRTMThresholdCopyLoop137.copy_final_tape _ _ _ _

private theorem one_add_le_square (width : Nat) : width+1≤(width+1)^2 := by
  have h := Nat.mul_le_mul_left (width+1) (by omega : 1≤width+1)
  simpa only [Nat.mul_one,pow_two] using h

theorem denBackup_length_le (archive numerator denominator depth : List Bool) :
    (denBackupTrace archive numerator denominator depth).length≤
      512*(numerator.length+denominator.length+depth.length+1)^2 := by
  have hp := prepare_length archive numerator denominator depth
  have hc := PSTRTMThresholdCopyCost138.copy_length_le (denArchive archive numerator) denominator depth numerator
  have he : denominator.length+depth.length+numerator.length+1=
      numerator.length+denominator.length+depth.length+1 := by omega
  rw [he] at hc
  have hq := one_add_le_square (numerator.length+denominator.length+depth.length)
  simp only [denBackupTrace,List.length_append,List.length_map]
  omega

theorem denBackup_visitedSpace_le (archive numerator denominator depth : List Bool) :
    visitedSpace denBackupMachine (archive.length+4*numerator.length+2*denominator.length+2*depth.length+11)
      (denBackupTrace archive numerator denominator depth)≤
      archive.length+4096*(numerator.length+denominator.length+depth.length+1)^2 := by
  have ht := denBackup_length_le archive numerator denominator depth
  have hs := PSTRTMTrace002.visitedSpace_le denBackupMachine
    (archive.length+4*numerator.length+2*denominator.length+2*depth.length+11)
    (denBackupTrace archive numerator denominator depth)
  have hq := one_add_le_square (numerator.length+denominator.length+depth.length)
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenBackup142
