module
public import Common.PSTR_TM_ThresholdDenBackup_142

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdPairCopies154
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBackup139

/-- Fixed485 labels. Both working operands are really copied from the
ORIGINAL risk/depth input. The original three fields and both sources
remain on the actual tape. There is no external workzone or frame oracle. -/
def copiesMachine : Machine 484 := PSTRTMSeq005.seqMachine backupMachine
  PSTRTMThresholdDenBackup142.denBackupMachine

def copiesTrace (risk : Rat) (depth : Nat) : List (MachineState 484) :=
  (backupTrace risk depth).map (PSTRTMSeq005.leftCfg (b:=170)) ++
    (PSTRTMThresholdDenBackup142.denBackupTrace [] (numerator risk) (denominator risk) (depthDigits depth)).map
      (PSTRTMSeq005.rightCfg (a:=313))

def copiesFinal (risk : Rat) (depth : Nat) : MachineState 484 :=
  PSTRTMSeq005.rightCfg (a:=313)
    (PSTRTMThresholdDenBackup142.denBackupFinal [] (numerator risk) (denominator risk) (depthDigits depth))

theorem copies_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    Runs copiesMachine (encode [.rational risk,.natural depth]) (copiesTrace risk depth) (copiesFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs backupMachine PSTRTMThresholdDenBackup142.denBackupMachine
    (encode [.rational risk,.natural depth]) (backupFinal risk depth)
    (PSTRTMThresholdDenBackup142.denBackupFinal [] (numerator risk) (denominator risk) (depthDigits depth))
    (backupTrace risk depth)
    (PSTRTMThresholdDenBackup142.denBackupTrace [] (numerator risk) (denominator risk) (depthDigits depth))
    (backup_runs risk depth hr)
  exact PSTRTMThresholdDenBackup142.denBackup_runsFrom [] _ _ _

theorem copies_final_tape (risk : Rat) (depth : Nat) :
    (copiesFinal risk depth).Tape=
      (PSTRTMThresholdDenBackup142.denBackupFinal [] (numerator risk) (denominator risk) (depthDigits depth)).Tape := rfl

private theorem arithmetic_length_bound (input width first second : Nat)
    (hf : first≤8192*(input+1)^2) (hs : second≤512*(width+1)^2) (hw : width ≤ input+1) :
    first+second≤16384*(input+1)^2 := by
  have h : width+1≤2*(input+1) := by omega
  have h2 := Nat.pow_le_pow_left h 2
  nlinarith

theorem copies_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    (copiesTrace risk depth).length≤16384*((encode [.rational risk,.natural depth]).length+1)^2 := by
  have hf := backup_length_le risk depth hr
  have hs := PSTRTMThresholdDenBackup142.denBackup_length_le [] (numerator risk) (denominator risk) (depthDigits depth)
  have hw := original_width_le risk depth hr
  simp only [copiesTrace,List.length_append,List.length_map]
  exact arithmetic_length_bound _ _ _ _ hf hs hw

private theorem arithmetic_space_bound (input time space : Nat)
    (ht : time≤16384*(input+1)^2) (hs : space ≤ input+2*time+1) :
    space≤65536*(input+1)^2 := by nlinarith

theorem copies_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    visitedSpace copiesMachine (encode [.rational risk,.natural depth]).length (copiesTrace risk depth)≤
      65536*((encode [.rational risk,.natural depth]).length+1)^2 :=
  arithmetic_space_bound _ _ _ (copies_length_le risk depth hr)
    (PSTRTMTrace002.visitedSpace_le copiesMachine (encode [.rational risk,.natural depth]).length (copiesTrace risk depth))

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdPairCopies154
