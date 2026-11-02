module
public import Common.PSTR_TM_ThresholdDenominator_200
public import Common.PSTR_TM_ThresholdDenominatorCost_201

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBadFactor226
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBReblock195 PSTRTMThresholdDenominatorFrame199

/-! The actual integer multiplier needed by the original bad-risk update.
This reuses only the FIRST increment/double half of the frozen denominator
program. B, the whole source risk archive, and BOTH near guards survive.
The output is a flagged work field, not the original bad-risk Rat Datum. -/

def factor (risk : Rat) (depth : Nat) : Nat :=
  2*(PaperProofs.Statistics.controllerB risk depth+1)

/-- Fixed1331 labels, before ALL risk/depth and without a supplied B. -/
def factorMachine : Machine 1330 := PSTRTMSeq005.seqMachine savedMachine firstMachine

def factorTrace (risk : Rat) (depth : Nat) : List (MachineState 1330) :=
  (savedTrace risk depth).map (PSTRTMSeq005.leftCfg (b := 38)) ++
    (firstTrace (savedLeft risk depth) (PaperProofs.Statistics.controllerB risk depth)).map
      (PSTRTMSeq005.rightCfg (a := 1291))

def factorFinal (risk : Rat) (depth : Nat) : MachineState 1330 :=
  PSTRTMSeq005.rightCfg (a := 1291)
    (firstFinal (savedLeft risk depth) (PaperProofs.Statistics.controllerB risk depth))

theorem factor_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    Runs factorMachine (encode [.rational risk,.natural depth])
      (factorTrace risk depth) (factorFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs savedMachine firstMachine
    (encode [.rational risk,.natural depth]) (savedFinal risk depth)
    (firstFinal (savedLeft risk depth) (PaperProofs.Statistics.controllerB risk depth))
    (savedTrace risk depth)
    (firstTrace (savedLeft risk depth) (PaperProofs.Statistics.controllerB risk depth))
    (saved_runs risk depth hr hd)
  rw [saved_final_tape]
  exact first_runsFrom _ _

theorem factor_final_tape (risk : Rat) (depth : Nat) :
    (factorFinal risk depth).Tape = Turing.Tape.mk₂ (false::savedLeft risk depth)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (factor risk depth))) := by
  change (firstFinal _ _).Tape = _
  exact first_final_tape _ _

theorem first_time_le (archive : List Bool) (value : Nat) :
    (firstTrace archive value).length ≤ 64*(natBits value+1) := by
  have h := denominator_length_le archive value
  simp only [denominatorTrace,List.length_append,List.length_map] at h
  omega

theorem factor_time_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (factorTrace risk depth).length ≤
      33554432*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have hm := PSTRTMThresholdBReblockCost196.saved_length_le risk depth hr hd
  have ha := first_time_le (savedLeft risk depth) (PaperProofs.Statistics.controllerB risk depth)
  have hw := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  have hs : (encode [.rational risk,.natural depth]).length+1 ≤
      ((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
    have hp : 1 ≤ (encode [.rational risk,.natural depth]).length+depth+1 := by omega
    have hc := Nat.pow_le_pow_right hp (by decide : 1 ≤ 3)
    simp only [pow_one] at hc
    omega
  simp only [factorTrace,List.length_append,List.length_map]
  omega

theorem factor_bits_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    natBits (factor risk depth) ≤ (encode [.rational risk,.natural depth]).length+6 := by
  have hb := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  have hi := PSTRTMArithmetic008.natBits_add_le (PaperProofs.Statistics.controllerB risk depth) 1
  have ho : natBits 1 = 1 := by decide
  rw [ho] at hi
  have hdbl := double_width (PaperProofs.Statistics.controllerB risk depth+1) (by omega)
  dsimp only [factor]
  omega

theorem factor_prefix_space_le (risk : Rat) (depth clock : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    visitedSpace factorMachine (encode [.rational risk,.natural depth]).length
      ((factorTrace risk depth).take clock) ≤
      134217728*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have ht := factor_time_le risk depth hr hd
  have hs := PSTRTMTrace002.visitedSpace_le factorMachine
    (encode [.rational risk,.natural depth]).length ((factorTrace risk depth).take clock)
  have hl : ((factorTrace risk depth).take clock).length ≤ (factorTrace risk depth).length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hc : (encode [.rational risk,.natural depth]).length+1 ≤
      ((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
    have hp : 1 ≤ (encode [.rational risk,.natural depth]).length+depth+1 := by omega
    have he := Nat.pow_le_pow_right hp (by decide : 1 ≤ 3)
    simp only [pow_one] at he
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBadFactor226
