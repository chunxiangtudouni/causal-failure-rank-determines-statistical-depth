module
public import Common.PSTR_TM_ThresholdStrip_113
public import Common.PSTR_TM_NatValue_017
public import Common.PSTR_TM_Length_004

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRisk114
open PaperProofs.Common.Native.RationalControllerComputation

def first (risk : Rat) : List Bool := PSTRTMNatValue017.rawPayload risk.num.natAbs
def second (risk : Rat) : List Bool := PSTRTMNatValue017.rawPayload risk.den
def depthSuffix (depth : Nat) : List Bool := false::(encodeNat depth++[true])
def riskMachine : Machine 143 := PSTRTMSeq005.seqMachine PSTRTMThresholdStrip113.stripMachine PSTRTMTwoRawOperands029.twoOperandMachine
def riskTrace (risk : Rat) (depth : Nat) : List (MachineState 143) :=
  (PSTRTMThresholdStrip113.stripTrace (PSTRTMThresholdStrip113.rawSuffix risk depth)).map (PSTRTMSeq005.leftCfg (b:=128)) ++
    (PSTRTMTwoRawOperands029.twoOperandTrace (first risk) (second risk) (depthSuffix depth)).map (PSTRTMSeq005.rightCfg (a:=14))
def riskFinal (risk : Rat) (depth : Nat) : MachineState 143 := PSTRTMSeq005.rightCfg (a:=14)
  (PSTRTMTwoRawOperands029.twoOperandFinal (first risk) (second risk) (depthSuffix depth))

theorem suffix_encoding (risk : Rat) (depth : Nat) : PSTRTMThresholdStrip113.rawSuffix risk depth=
    PSTRTMTwoRawOperands029.rawInput (first risk)++PSTRTMTwoRawOperands029.rawInput (second risk)++depthSuffix depth := by
  simp [PSTRTMThresholdStrip113.rawSuffix,PSTRTMTwoRawOperands029.rawInput,first,second,depthSuffix,
    PSTRTMNatValue017.rawPayload,encodeNat,List.append_assoc]

/-- ORIGINAL threshold input is actually parsed into the numerator and
denominator flagged fields. The original natural-depth tag/header/payload
and list end are preserved as the suffix, not supplied separately. -/
theorem risk_runs (risk : Rat) (depth : Nat) (hr : 0<risk) :
    Runs riskMachine (encode [.rational risk,.natural depth]) (riskTrace risk depth) (riskFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs PSTRTMThresholdStrip113.stripMachine PSTRTMTwoRawOperands029.twoOperandMachine
    (encode [.rational risk,.natural depth]) (PSTRTMThresholdStrip113.state 14 (PSTRTMThresholdStrip113.rawSuffix risk depth))
    (PSTRTMTwoRawOperands029.twoOperandFinal (first risk) (second risk) (depthSuffix depth))
    (PSTRTMThresholdStrip113.stripTrace (PSTRTMThresholdStrip113.rawSuffix risk depth))
    (PSTRTMTwoRawOperands029.twoOperandTrace (first risk) (second risk) (depthSuffix depth))
    (PSTRTMThresholdStrip113.threshold_strip_runs risk depth hr)
  have h := PSTRTMTwoRawOperands029.twoOperand_runs (first risk) (second risk) (depthSuffix depth)
  rw [PSTRTMThresholdStrip113.strip_final_tape,suffix_encoding]
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem risk_final_tape (risk : Rat) (depth : Nat) : (riskFinal risk depth).Tape=
    Turing.Tape.mk₂ (false::true::false::false::PSTRTMRawNat010.leftBlocks (first risk).reverse)
      (PSTRTMIncrement009.blocks (second risk)++false::depthSuffix depth) := rfl

theorem first_length (risk : Rat) : (first risk).length=natBits risk.num.natAbs := by
  simp only [first,PSTRTMNatValue017.rawPayload,List.length_ofFn]
theorem second_length (risk : Rat) : (second risk).length=natBits risk.den := by
  simp only [second,PSTRTMNatValue017.rawPayload,List.length_ofFn]
theorem original_widths_le (risk : Rat) (depth : Nat) (hr : 0<risk) :
    natBits risk.num.natAbs+natBits risk.den ≤ (encode [.rational risk,.natural depth]).length+1 := by
  rw [PSTRTMThresholdStrip113.original_input risk depth hr]
  simp only [PSTRTMThresholdStrip113.headerBits,PSTRTMThresholdStrip113.rawSuffix,List.length_append,List.length_cons,
    List.length_nil,PSTRTMLength004.encodeNat_length]
  omega

private theorem arithmetic_length_bound (n m input : Nat) (hw : n+m≤ input+1) :
    15+(n^2+m^2+27*n+11*m+35) ≤ 512*(input+1)^2 := by
  have hn : n≤ input+1 := by omega
  have hm : m≤ input+1 := by omega
  have hn2 := Nat.pow_le_pow_left hn 2
  have hm2 := Nat.pow_le_pow_left hm 2
  nlinarith

private theorem arithmetic_space_bound (input time space : Nat)
    (ht : time≤512*(input+1)^2) (hs : space≤ input+2*time+1) : space≤2048*(input+1)^2 := by
  nlinarith

theorem risk_length_le (risk : Rat) (depth : Nat) (hr : 0<risk) :
    (riskTrace risk depth).length ≤ 512*((encode [.rational risk,.natural depth]).length+1)^2 := by
  have hw := original_widths_le risk depth hr
  simp only [riskTrace,List.length_append,List.length_map,PSTRTMThresholdStrip113.strip_length,
    PSTRTMTwoRawOperands029.twoOperand_length,first_length,second_length]
  exact arithmetic_length_bound _ _ _ hw

theorem risk_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0<risk) :
    visitedSpace riskMachine (encode [.rational risk,.natural depth]).length (riskTrace risk depth) ≤
      2048*((encode [.rational risk,.natural depth]).length+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le riskMachine (encode [.rational risk,.natural depth]).length (riskTrace risk depth)
  have ht := risk_length_le risk depth hr
  exact arithmetic_space_bound _ _ _ ht hs

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRisk114
