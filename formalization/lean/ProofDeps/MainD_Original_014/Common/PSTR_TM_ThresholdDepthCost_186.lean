module
public import Common.PSTR_TM_ThresholdDepthProgram_185

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthCost186
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthSource184 PSTRTMThresholdDepthProgram185

private theorem arithmetic_budget (input depth width fieldLength gap : Nat)
    (hw : width ≤ input+4) (hf : fieldLength ≤ input+1) (hg : gap≤2*input+6) :
    PSTRTMThresholdDepthLoopBudget182.phaseBudget width fieldLength gap depth≤
      1048576*(input+depth+1)^2 := by
  let scale := input+depth+1
  have hs : 1≤scale := by dsimp only [scale]; omega
  have hw' : width≤4*scale := by dsimp only [scale]; omega
  have hf' : fieldLength≤scale := by dsimp only [scale]; omega
  have hg' : gap≤6*scale := by dsimp only [scale]; omega
  have hd' : depth≤scale := by dsimp only [scale]; omega
  have hw2 := Nat.pow_le_pow_left hw' 2
  have hwd := Nat.mul_le_mul hw' hd'
  have hs2 : scale≤scale^2 := by
    simpa only [Nat.mul_one,pow_two] using Nat.mul_le_mul_left scale hs
  change PSTRTMThresholdDepthLoopBudget182.phaseBudget width fieldLength gap depth≤1048576*scale^2
  unfold PSTRTMThresholdDepthLoopBudget182.phaseBudget
  nlinarith

theorem original_loop_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1≤depth) :
    (PSTRTMThresholdDepthLoopTrace179.loopTrace (riskArchive risk) (PSTRTMThresholdBackup139.depthDigits depth)
      (PaperProofs.Statistics.controllerB risk 1) (initialGap risk)).length≤
        1048576*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have ht := PSTRTMThresholdDepthLoopCost183.loop_length_le (riskArchive risk)
    (PSTRTMThresholdBackup139.depthDigits depth) (PaperProofs.Statistics.controllerB risk 1)
    (max (PaperProofs.Statistics.controllerB risk 1) 2) (initialGap risk) (depth_positive depth hd)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [depth_value,depth_length] at ht
  have hb := arithmetic_budget (encode [.rational risk,.natural depth]).length depth
    (natBits (max (PaperProofs.Statistics.controllerB risk 1) 2)) (natBits depth) (initialGap risk)
    (original_bound_bits_le risk depth hr) (PSTRTMThresholdFields118.depth_bits_le risk depth hr)
    (original_gap_le risk depth hr)
  apply ht.trans
  calc
    depth*PSTRTMThresholdDepthLoopBudget182.phaseBudget
        (natBits (max (PaperProofs.Statistics.controllerB risk 1) 2)) (natBits depth) (initialGap risk) depth≤
        ((encode [.rational risk,.natural depth]).length+depth+1)*
          (1048576*((encode [.rational risk,.natural depth]).length+depth+1)^2) :=
      Nat.mul_le_mul (by omega) hb
    _=1048576*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
      simp only [pow_succ,pow_zero,Nat.mul_comm,Nat.mul_left_comm]

private theorem arithmetic_time (input depth seed loop : Nat)
    (hs : seed≤32768*(input+1)^2) (hl : loop≤1048576*(input+depth+1)^3) :
    seed+loop≤2097152*(input+depth+1)^3 := by
  have hp : input+1 ≤ input+depth+1 := by omega
  have hp2 := Nat.pow_le_pow_left hp 2
  have hscale : 1 ≤ input+depth+1 := by omega
  have hscale3 : (input+depth+1)^2≤(input+depth+1)^3 := by
    exact Nat.pow_le_pow_right hscale (by decide : 2≤3)
  have hs' := hs.trans (Nat.mul_le_mul_left 32768 (hp2.trans hscale3))
  omega

/-- Original encoded input plus the original depth budget, with no
answer/width/fuel field. SAME actual1190-label trace and fixed constants.
This still ends in flagged B, not the original five-Datum output. -/
theorem depth_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1≤depth) :
    (depthTrace risk depth).length≤2097152*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have hs := PSTRTMThresholdSeed155.seed_length_le risk depth hr
  have hl := original_loop_length_le risk depth hr hd
  simp only [depthTrace,List.length_append,List.length_map]
  exact arithmetic_time _ _ _ _ hs hl

theorem depth_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1≤depth) :
    visitedSpace depthMachine (encode [.rational risk,.natural depth]).length (depthTrace risk depth)≤
      8388608*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have ht := depth_length_le risk depth hr hd
  have hs := PSTRTMTrace002.visitedSpace_le depthMachine (encode [.rational risk,.natural depth]).length (depthTrace risk depth)
  have hp : 1≤(encode [.rational risk,.natural depth]).length+depth+1 := by omega
  have hp2 : (encode [.rational risk,.natural depth]).length+depth+1≤
      ((encode [.rational risk,.natural depth]).length+depth+1)^2 := by
    simpa only [pow_two,Nat.mul_one] using
      Nat.mul_le_mul_left ((encode [.rational risk,.natural depth]).length+depth+1) hp
  have hp3 : ((encode [.rational risk,.natural depth]).length+depth+1)^2≤
      ((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
    exact Nat.pow_le_pow_right hp (by decide : 2≤3)
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthCost186
