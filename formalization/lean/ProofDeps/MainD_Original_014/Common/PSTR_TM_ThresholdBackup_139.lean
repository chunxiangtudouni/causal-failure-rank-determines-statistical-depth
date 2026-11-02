module
public import Common.PSTR_TM_ThresholdCopyCost_138

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBackup139
open PaperProofs.Common.Native.RationalControllerComputation

def numerator (risk : Rat) : List Bool := PSTRTMThresholdSource125.first risk
def denominator (risk : Rat) : List Bool := PSTRTMThresholdSource125.second risk
def depthDigits (depth : Nat) : List Bool := PSTRTMThresholdSource125.depthDigits depth

/-- Fixed314-label ORIGINAL threshold-input front end. All three fields
are actually decoded, actual shuttles reach NUM, and the fixed copier
really appends a canonical flagged NUM backup to the right. The original
risk/depth fields remain in its real left archive. This is NOT the original
five-Datum threshold output or the missing AB-column loader. -/
def backupMachine : Machine 313 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdSource125.sourceMachine PSTRTMThresholdCopyCode126.copyMachine

def backupTrace (risk : Rat) (depth : Nat) : List (MachineState 313) :=
  (PSTRTMThresholdSource125.sourceTrace risk depth).map (PSTRTMSeq005.leftCfg (b:=130)) ++
    (PSTRTMThresholdCopyLoop137.copyTrace [] (numerator risk) (denominator risk) (depthDigits depth)).map (PSTRTMSeq005.rightCfg (a:=182))

def backupFinal (risk : Rat) (depth : Nat) : MachineState 313 := PSTRTMSeq005.rightCfg (a:=182)
  (PSTRTMThresholdCopyLoop137.copyFinal [] (numerator risk) (denominator risk) (depthDigits depth))

theorem backup_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    Runs backupMachine (encode [.rational risk,.natural depth]) (backupTrace risk depth) (backupFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs PSTRTMThresholdSource125.sourceMachine PSTRTMThresholdCopyCode126.copyMachine
    (encode [.rational risk,.natural depth]) (PSTRTMThresholdSource125.sourceFinal risk depth)
    (PSTRTMThresholdCopyLoop137.copyFinal [] (numerator risk) (denominator risk) (depthDigits depth))
    (PSTRTMThresholdSource125.sourceTrace risk depth)
    (PSTRTMThresholdCopyLoop137.copyTrace [] (numerator risk) (denominator risk) (depthDigits depth))
    (PSTRTMThresholdSource125.source_runs risk depth hr)
  have h := PSTRTMThresholdCopyLoop137.copy_runsFrom [] (numerator risk) (denominator risk) (depthDigits depth)
  rw [PSTRTMThresholdSource125.source_final_tape]
  simpa only [PSTRTMThresholdCopyLoop137.copyInitial,PSTRTMThresholdCopyCode126.state,
    Turing.Tape.mk₁,Turing.Tape.mk₂,PSTRTMRawNat010.blank_single_false,numerator,denominator,depthDigits] using h

theorem backup_final_tape (risk : Rat) (depth : Nat) : (backupFinal risk depth).Tape=Turing.Tape.mk₂
    (false::true::false::false::(PSTRTMRawNat010.leftBlocks (depthDigits depth).reverse++false::false::
      (PSTRTMRawNat010.leftBlocks (denominator risk).reverse++false::true::false::false::
        (PSTRTMRawNat010.leftBlocks (numerator risk).reverse++[false]))))
    (PSTRTMIncrement009.blocks (numerator risk)) := PSTRTMThresholdCopyLoop137.copy_final_tape _ _ _ _

theorem original_width_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    (numerator risk).length+(denominator risk).length+(depthDigits depth).length ≤
      (encode [.rational risk,.natural depth]).length+1 := by
  rw [PSTRTMThresholdStrip113.original_input risk depth hr]
  simp only [numerator,denominator,depthDigits,PSTRTMThresholdSource125.first,PSTRTMThresholdSource125.second,
    PSTRTMThresholdSource125.depthDigits,PSTRTMThresholdRisk114.first_length,PSTRTMThresholdRisk114.second_length,
    PSTRTMNatValue017.rawPayload,List.length_ofFn,PSTRTMThresholdStrip113.headerBits,PSTRTMThresholdStrip113.rawSuffix,
    List.length_append,List.length_cons,List.length_nil,PSTRTMLength004.encodeNat_length]
  omega

private theorem arithmetic_length_bound (input width source copy : Nat)
    (hs : source≤4096*(input+1)^2) (hc : copy≤256*(width+1)^2) (hw : width ≤ input+1) :
    source+copy≤8192*(input+1)^2 := by
  have hh : width+1≤2*(input+1) := by omega
  have hh2 := Nat.pow_le_pow_left hh 2
  nlinarith

theorem backup_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    (backupTrace risk depth).length≤8192*((encode [.rational risk,.natural depth]).length+1)^2 := by
  have hs := PSTRTMThresholdSource125.source_length_le risk depth hr
  have hc := PSTRTMThresholdCopyCost138.copy_length_le [] (numerator risk) (denominator risk) (depthDigits depth)
  have hw := original_width_le risk depth hr
  simp only [backupTrace,List.length_append,List.length_map]
  exact arithmetic_length_bound _ _ _ _ hs hc hw

private theorem arithmetic_space_bound (input time space : Nat)
    (ht : time≤8192*(input+1)^2) (hs : space ≤ input+2*time+1) : space≤32768*(input+1)^2 := by nlinarith

theorem backup_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    visitedSpace backupMachine (encode [.rational risk,.natural depth]).length (backupTrace risk depth)≤
      32768*((encode [.rational risk,.natural depth]).length+1)^2 :=
  arithmetic_space_bound _ _ _ (backup_length_le risk depth hr)
    (PSTRTMTrace002.visitedSpace_le backupMachine (encode [.rational risk,.natural depth]).length (backupTrace risk depth))

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBackup139
