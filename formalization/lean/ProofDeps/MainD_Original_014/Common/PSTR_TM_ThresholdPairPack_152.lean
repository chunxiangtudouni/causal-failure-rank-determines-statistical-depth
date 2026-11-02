module
public import Common.PSTR_TM_ThresholdPairRewind_151

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdPairPack152
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdPairRewind151

/-- Fixed203 labels: the actual nine-label working NUM rewind and the
new194-label packer with genuine right padding. All retained risk/depth
source cells behind the real false guard remain physical archived data. -/
def packedMachine : Machine 202 := PSTRTMSeq005.seqMachine rewindMachine PSTRTMPackFrameCode146.packMachine

def packedTrace (archive numerator denominator depth : List Bool) : List (MachineState 202) :=
  (rewindTrace archive numerator denominator depth).map (PSTRTMSeq005.leftCfg (b:=193)) ++
    (PSTRTMPackFrameRun149.packTrace (workArchive archive numerator denominator depth) [] numerator denominator).map
      (PSTRTMSeq005.rightCfg (a:=8))

def packedFinal (archive numerator denominator depth : List Bool) : MachineState 202 :=
  PSTRTMSeq005.rightCfg (a:=8)
    (PSTRTMPackFrameRun149.final (workArchive archive numerator denominator depth) [] numerator denominator)

theorem packed_runsFrom (archive numerator denominator depth : List Bool) :
    PSTRTMSeq005.RunsFrom packedMachine
      ⟨0,(PSTRTMThresholdDenBackup142.denBackupFinal archive numerator denominator depth).Tape⟩
      (packedTrace archive numerator denominator depth) (packedFinal archive numerator denominator depth) := by
  apply PSTRTMSeq005.seq_runsFrom rewindMachine PSTRTMPackFrameCode146.packMachine
    ⟨0,(PSTRTMThresholdDenBackup142.denBackupFinal archive numerator denominator depth).Tape⟩
    (rewindFinal archive numerator denominator depth)
    (PSTRTMPackFrameRun149.final (workArchive archive numerator denominator depth) [] numerator denominator)
    (rewindTrace archive numerator denominator depth)
    (PSTRTMPackFrameRun149.packTrace (workArchive archive numerator denominator depth) [] numerator denominator)
    (rewind_runsFrom _ _ _ _)
  rw [rewind_final_tape]
  exact PSTRTMPackFrameRun149.pack_runsFrom _ _ _

/-- ENTIRE tape at actual first A data. Input working copies have become
exact zero-extended A/B columns. Original NUM/DEN/DEPTH and archive remain
behind the real guard; no free frame or uncharged physical reset is used. -/
theorem packed_final_tape (archive numerator denominator depth : List Bool) :
    (packedFinal archive numerator denominator depth).Tape=Turing.Tape.mk₂
      (false::workArchive archive numerator denominator depth)
      (PSTRTMBinaryAdd024.operandColumns (PSTRTMPackCode036.digitPairs numerator denominator)) :=
  PSTRTMPackFrameRun149.pack_final_tape _ _ _

private theorem one_add_le_square (width : Nat) : width+1≤(width+1)^2 := by
  have h := Nat.mul_le_mul_left (width+1) (by omega : 1≤width+1)
  simpa only [Nat.mul_one,pow_two] using h

theorem packed_length_le (archive numerator denominator depth : List Bool) :
    (packedTrace archive numerator denominator depth).length≤512*(numerator.length+denominator.length+1)^2 := by
  have hr := rewind_length archive numerator denominator depth
  have hp := PSTRTMPackFrameCost150.initial_pack_length_le
    (workArchive archive numerator denominator depth) numerator denominator
  have hq := one_add_le_square (numerator.length+denominator.length)
  simp only [packedTrace,List.length_append,List.length_map]
  omega

theorem packed_visitedSpace_le (archive numerator denominator depth : List Bool) :
    visitedSpace packedMachine
      (archive.length+4*numerator.length+4*denominator.length+2*depth.length+15)
      (packedTrace archive numerator denominator depth)≤
      archive.length+2*depth.length+4096*(numerator.length+denominator.length+1)^2 := by
  have ht := packed_length_le archive numerator denominator depth
  have hs := PSTRTMTrace002.visitedSpace_le packedMachine
    (archive.length+4*numerator.length+4*denominator.length+2*depth.length+15)
    (packedTrace archive numerator denominator depth)
  have hq := one_add_le_square (numerator.length+denominator.length)
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdPairPack152
