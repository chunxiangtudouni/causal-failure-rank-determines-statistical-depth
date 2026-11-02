module
public import Common.PSTR_TM_ThresholdUnitColumnsCost_160
public import Common.PSTR_TM_ThresholdAddTwoFrame_161
public import Common.PSTR_TM_B1ResidentFrame_123

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdNextFrame162
open PaperProofs.Common.Native.RationalControllerComputation

/-- Fixed244 labels: two binary increments, followed by the actual
right-insertion ONE/B loader. All physical movement is in these traces. -/
def operandsMachine : Machine 243 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdAddTwoFrame161.addTwoMachine PSTRTMThresholdUnitColumnsCode156.unitMachine

def operandsTrace (archive : List Bool) (value : Nat) : List (MachineState 243) :=
  (PSTRTMThresholdAddTwoFrame161.addTwoTrace archive value).map (PSTRTMSeq005.leftCfg (b:=213)) ++
    (PSTRTMThresholdUnitColumnsRun159.loopTrace archive [] true (PSTRTMNatValue017.rawPayload (value+2))).map
      (PSTRTMSeq005.rightCfg (a:=29))

def operandsFinal (archive : List Bool) (value : Nat) : MachineState 243 :=
  PSTRTMSeq005.rightCfg (a:=29)
    (PSTRTMThresholdUnitColumnsRun159.final archive [] true (PSTRTMNatValue017.rawPayload (value+2)))

theorem operands_runsFrom (archive : List Bool) (value : Nat) :
    PSTRTMSeq005.RunsFrom operandsMachine
      ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩
      (operandsTrace archive value) (operandsFinal archive value) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMThresholdAddTwoFrame161.addTwoMachine PSTRTMThresholdUnitColumnsCode156.unitMachine
    ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩
    (PSTRTMThresholdAddTwoFrame161.addTwoFinal archive value)
    (PSTRTMThresholdUnitColumnsRun159.final archive [] true (PSTRTMNatValue017.rawPayload (value+2)))
    (PSTRTMThresholdAddTwoFrame161.addTwoTrace archive value)
    (PSTRTMThresholdUnitColumnsRun159.loopTrace archive [] true (PSTRTMNatValue017.rawPayload (value+2)))
    (PSTRTMThresholdAddTwoFrame161.addTwo_runsFrom archive value)
  rw [PSTRTMThresholdAddTwoFrame161.addTwo_final_tape]
  exact PSTRTMThresholdUnitColumnsRun159.unit_columns_runsFrom _ _

theorem operands_final_tape (archive : List Bool) (value : Nat) :
    (operandsFinal archive value).Tape=Turing.Tape.mk₂ (false::archive)
      (PSTRTMBinaryAdd024.operandColumns (PSTRTMB1ResidentFrame123.sourcePairs 1 (value+2))) :=
  PSTRTMThresholdUnitColumnsCost160.natural_unit_columns_final_tape _ _

/-- Fixed358-label resident threshold recurrence. All inputs are actual
canonical flagged B cells and archived data; neither an answer nor any
width/fuel/quota cost parameter enters the finite code. The result is
canonical flagged clog2(B+2), not a raw Datum encoder or five-output call. -/
def nextMachine : Machine 357 := PSTRTMSeq005.seqMachine operandsMachine PSTRTMB1ResidentFrame123.residentMachine

def nextTrace (archive : List Bool) (value : Nat) : List (MachineState 357) :=
  (operandsTrace archive value).map (PSTRTMSeq005.leftCfg (b:=113)) ++
    (PSTRTMB1ResidentFrame123.residentTrace archive 1 (value+2)).map (PSTRTMSeq005.rightCfg (a:=243))

def nextFinal (archive : List Bool) (value : Nat) : MachineState 357 :=
  PSTRTMSeq005.rightCfg (a:=243) (PSTRTMB1ResidentFrame123.residentFinal archive 1 (value+2))

theorem next_runsFrom (archive : List Bool) (value : Nat) :
    PSTRTMSeq005.RunsFrom nextMachine
      ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩
      (nextTrace archive value) (nextFinal archive value) := by
  apply PSTRTMSeq005.seq_runsFrom operandsMachine PSTRTMB1ResidentFrame123.residentMachine
    ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩
    (operandsFinal archive value) (PSTRTMB1ResidentFrame123.residentFinal archive 1 (value+2))
    (operandsTrace archive value) (PSTRTMB1ResidentFrame123.residentTrace archive 1 (value+2))
    (operands_runsFrom archive value)
  rw [operands_final_tape]
  exact PSTRTMB1ResidentFrame123.resident_runsFrom _ _ _ (by decide)

theorem next_final_tape (archive : List Bool) (value : Nat) :
    (nextFinal archive value).Tape=Turing.Tape.mk₂
      (List.replicate (4*PSTRTMB1RunFrame122.width 1 (value+2)+5) false++archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (Nat.clog 2 (value+2)))) := by
  have h := PSTRTMB1ResidentFrame123.resident_final_tape archive 1 (value+2)
  simpa only [nextFinal,PSTRTMSeq005.rightCfg,PSTRTMB1Value068.exponent,Nat.cast_one,div_one,
    Nat.ceil_natCast] using h

private theorem operands_arithmetic (width input first second : Nat)
    (hw : width ≤ input+2) (hf : first≤32*(input+1)) (hs : second≤64*(width+1)^2) :
    first+second≤1024*(input+1)^2 := by
  have he : width+1 ≤ input+3 := by omega
  have he2 := Nat.pow_le_pow_left he 2
  nlinarith

theorem operands_length_le (archive : List Bool) (value : Nat) :
    (operandsTrace archive value).length≤1024*(natBits value+1)^2 := by
  have hf := PSTRTMThresholdAddTwoFrame161.addTwo_length_le archive value
  have hs := PSTRTMThresholdUnitColumnsCost160.unit_columns_length_le archive (PSTRTMNatValue017.rawPayload (value+2))
  have hw := PSTRTMArithmetic008.natBits_add_le value 2
  have ht : natBits 2=2 := by decide
  rw [ht] at hw
  have hl : (PSTRTMNatValue017.rawPayload (value+2)).length=natBits (value+2) := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  rw [hl] at hs
  simp only [operandsTrace,List.length_append,List.length_map]
  exact operands_arithmetic _ _ _ _ hw hf hs

private theorem next_arithmetic (width input first second : Nat)
    (hw : width ≤ input+2) (hf : first≤1024*(input+1)^2) (hs : second≤256*(1+width+1)^2) :
    first+second≤8192*(input+1)^2 := by
  have he : 1+width+1 ≤ input+4 := by omega
  have he2 := Nat.pow_le_pow_left he 2
  nlinarith

theorem next_length_le (archive : List Bool) (value : Nat) :
    (nextTrace archive value).length≤8192*(natBits value+1)^2 := by
  have hf := operands_length_le archive value
  have hs := PSTRTMB1ResidentFrame123.resident_length_le archive 1 (value+2) (by decide)
  have hw := PSTRTMArithmetic008.natBits_add_le value 2
  have h1 : natBits 1=1 := by decide
  have h2 : natBits 2=2 := by decide
  rw [h1] at hs
  rw [h2] at hw
  simp only [nextTrace,List.length_append,List.length_map]
  exact next_arithmetic _ _ _ _ hw hf hs

theorem next_visitedSpace_le (archive : List Bool) (value : Nat) :
    visitedSpace nextMachine (archive.length+1+2*natBits value) (nextTrace archive value)≤
      archive.length+32768*(natBits value+1)^2 := by
  have ht := next_length_le archive value
  have hs := PSTRTMTrace002.visitedSpace_le nextMachine (archive.length+1+2*natBits value) (nextTrace archive value)
  nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdNextFrame162
