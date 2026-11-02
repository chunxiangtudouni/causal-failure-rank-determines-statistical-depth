module
public import Common.PSTR_TM_ThresholdPairPack_152
public import Common.PSTR_TM_B1ResidentFrame_123

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdB1Prepared153
open PaperProofs.Common.Native.RationalControllerComputation

def numeratorDigits (numerator : Nat) : List Bool := PSTRTMNatValue017.rawPayload numerator
def denominatorDigits (denominator : Nat) : List Bool := PSTRTMNatValue017.rawPayload denominator

def retainedArchive (archive : List Bool) (numerator denominator : Nat) (depth : List Bool) : List Bool :=
  PSTRTMThresholdPairRewind151.workArchive archive (numeratorDigits numerator) (denominatorDigits denominator) depth

/-- Fixed317 labels: actual rewind/packing of the real working copies,
then the already frozen genuine archive-preserving123 B1 program. This
is still an internal numerical seed call, not a five-output threshold. -/
def preparedMachine : Machine 316 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdPairPack152.packedMachine PSTRTMB1ResidentFrame123.residentMachine

def preparedTrace (archive : List Bool) (numerator denominator : Nat) (depth : List Bool) : List (MachineState 316) :=
  (PSTRTMThresholdPairPack152.packedTrace archive (numeratorDigits numerator) (denominatorDigits denominator) depth).map
    (PSTRTMSeq005.leftCfg (b:=113)) ++
  (PSTRTMB1ResidentFrame123.residentTrace (retainedArchive archive numerator denominator depth) numerator denominator).map
    (PSTRTMSeq005.rightCfg (a:=202))

def preparedFinal (archive : List Bool) (numerator denominator : Nat) (depth : List Bool) : MachineState 316 :=
  PSTRTMSeq005.rightCfg (a:=202)
    (PSTRTMB1ResidentFrame123.residentFinal (retainedArchive archive numerator denominator depth) numerator denominator)

theorem prepared_runsFrom (archive : List Bool) (numerator denominator : Nat) (depth : List Bool) (hn : 0 < numerator) :
    PSTRTMSeq005.RunsFrom preparedMachine
      ⟨0,(PSTRTMThresholdDenBackup142.denBackupFinal archive (numeratorDigits numerator) (denominatorDigits denominator) depth).Tape⟩
      (preparedTrace archive numerator denominator depth) (preparedFinal archive numerator denominator depth) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMThresholdPairPack152.packedMachine PSTRTMB1ResidentFrame123.residentMachine
    ⟨0,(PSTRTMThresholdDenBackup142.denBackupFinal archive (numeratorDigits numerator) (denominatorDigits denominator) depth).Tape⟩
    (PSTRTMThresholdPairPack152.packedFinal archive (numeratorDigits numerator) (denominatorDigits denominator) depth)
    (PSTRTMB1ResidentFrame123.residentFinal (retainedArchive archive numerator denominator depth) numerator denominator)
    (PSTRTMThresholdPairPack152.packedTrace archive (numeratorDigits numerator) (denominatorDigits denominator) depth)
    (PSTRTMB1ResidentFrame123.residentTrace (retainedArchive archive numerator denominator depth) numerator denominator)
    (PSTRTMThresholdPairPack152.packed_runsFrom _ _ _ _)
  rw [PSTRTMThresholdPairPack152.packed_final_tape]
  exact PSTRTMB1ResidentFrame123.resident_runsFrom _ _ _ hn

theorem prepared_final_tape (archive : List Bool) (numerator denominator : Nat) (depth : List Bool) :
    (preparedFinal archive numerator denominator depth).Tape=Turing.Tape.mk₂
      (List.replicate (4*PSTRTMB1RunFrame122.width numerator denominator+5) false++
        retainedArchive archive numerator denominator depth)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PSTRTMB1Value068.exponent numerator denominator))) :=
  PSTRTMB1ResidentFrame123.resident_final_tape _ _ _

theorem prepared_length_le (archive : List Bool) (numerator denominator : Nat) (depth : List Bool) (hn : 0 < numerator) :
    (preparedTrace archive numerator denominator depth).length≤1024*(natBits numerator+natBits denominator+1)^2 := by
  have hp := PSTRTMThresholdPairPack152.packed_length_le archive (numeratorDigits numerator) (denominatorDigits denominator) depth
  have hb := PSTRTMB1ResidentFrame123.resident_length_le (retainedArchive archive numerator denominator depth) numerator denominator hn
  have hnlen : (numeratorDigits numerator).length=natBits numerator := by
    simp only [numeratorDigits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have hdlen : (denominatorDigits denominator).length=natBits denominator := by
    simp only [denominatorDigits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  rw [hnlen,hdlen] at hp
  simp only [preparedTrace,List.length_append,List.length_map]
  omega

private theorem one_add_le_square (width : Nat) : width+1≤(width+1)^2 := by
  have h := Nat.mul_le_mul_left (width+1) (by omega : 1≤width+1)
  simpa only [Nat.mul_one,pow_two] using h

theorem prepared_visitedSpace_le (archive : List Bool) (numerator denominator : Nat) (depth : List Bool) (hn : 0 < numerator) :
    visitedSpace preparedMachine
      (archive.length+4*natBits numerator+4*natBits denominator+2*depth.length+15)
      (preparedTrace archive numerator denominator depth)≤
      archive.length+2*depth.length+8192*(natBits numerator+natBits denominator+1)^2 := by
  have ht := prepared_length_le archive numerator denominator depth hn
  have hs := PSTRTMTrace002.visitedSpace_le preparedMachine
    (archive.length+4*natBits numerator+4*natBits denominator+2*depth.length+15)
    (preparedTrace archive numerator denominator depth)
  have hq := one_add_le_square (natBits numerator+natBits denominator)
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdB1Prepared153
