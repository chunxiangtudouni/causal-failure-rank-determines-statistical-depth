module
public import Common.PSTR_TM_ThresholdBadSource_229

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRiskReturnBudget230
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthLoopTrace179 PSTRTMThresholdDepthLoopNext177
open PSTRTMThresholdCountdownCode164 PSTRTMThresholdDepthLoopValue181
open PSTRTMThresholdDepthLoopBudget182 PSTRTMThresholdBBackupEntry188

/-! Cost of physically crossing the SAME exhausted-depth/gap archive.
The gap is the actual layout outcome of the frozen loop, never a supplied
workspace or input certificate. Every extra gap was created by a real
previous Bnext call and grows at most seven times the bounded bit width. -/

theorem outcome_gap_le (depth : List Bool) (value bound gap : Nat)
    (hp : true∈depth) (hv : value ≤ bound) (hb : 2 ≤ bound) :
    (outcome depth value gap).gap ≤ gap+7*natBits bound*PSTRTMIncrement009.valueDigits depth := by
  by_cases hone : PSTRTMIncrement009.valueDigits depth = 1
  · rw [outcome_zero depth value gap hp hone]
    change gap ≤ gap+7*natBits bound*PSTRTMIncrement009.valueDigits depth
    omega
  · have hnext := outcome_gap_le (predDigits depth) (nextValue value) bound (nextGap value gap)
      (pred_positive depth hp hone) (nextValue_le_bound value bound hv hb) hb
    have hg := nextGap_le value bound gap hv hb
    have hpred := pred_value depth hp
    have he : PSTRTMIncrement009.valueDigits depth =
        PSTRTMIncrement009.valueDigits (predDigits depth)+1 := by omega
    rw [outcome_step depth value gap hp hone]
    calc
      _ ≤ nextGap value gap+7*natBits bound*PSTRTMIncrement009.valueDigits (predDigits depth) := hnext
      _ ≤ gap+7*natBits bound+7*natBits bound*PSTRTMIncrement009.valueDigits (predDigits depth) :=
        Nat.add_le_add_right hg _
      _ = gap+7*natBits bound*PSTRTMIncrement009.valueDigits depth := by
        rw [he,Nat.mul_add,Nat.mul_one]
        omega
termination_by PSTRTMIncrement009.valueDigits depth
decreasing_by
  have h := pred_value depth hp
  omega

theorem result_depth_length (risk : Rat) (depth : Nat) (hd : 1 ≤ depth) :
    (result risk depth).depth.length = natBits depth := by
  have hp := PSTRTMThresholdDepthSource184.depth_positive depth hd
  have h := outcome_properties (PSTRTMThresholdBackup139.depthDigits depth)
    (PaperProofs.Statistics.controllerB risk 1) (PSTRTMThresholdDepthSource184.initialGap risk) hp
  exact h.1.trans (PSTRTMThresholdDepthSource184.depth_length depth)

theorem result_depth_ne_nil (risk : Rat) (depth : Nat) (hd : 1 ≤ depth) :
    (result risk depth).depth ≠ [] := by
  have hl := result_depth_length risk depth hd
  have hb : 0 < natBits depth := by simp [natBits]
  intro he
  rw [he,List.length_nil] at hl
  omega

private theorem arithmetic_gap (input depth gap width initial : Nat)
    (hg : gap ≤ initial+7*width*depth) (hi : initial ≤ 2*input+6) (hw : width ≤ input+4) :
    gap ≤ 64*(input+depth+1)^2 := by
  have hm := Nat.mul_le_mul_right depth (Nat.mul_le_mul_left 7 hw)
  have ha : gap ≤ 2*input+6+7*(input+4)*depth := by omega
  nlinarith [Nat.zero_le (input^2),Nat.zero_le (depth^2)]

theorem result_gap_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (result risk depth).gap ≤ 64*((encode [.rational risk,.natural depth]).length+depth+1)^2 := by
  have hp := PSTRTMThresholdDepthSource184.depth_positive depth hd
  have hg := outcome_gap_le (PSTRTMThresholdBackup139.depthDigits depth)
    (PaperProofs.Statistics.controllerB risk 1) (max (PaperProofs.Statistics.controllerB risk 1) 2)
    (PSTRTMThresholdDepthSource184.initialGap risk) hp (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [PSTRTMThresholdDepthSource184.depth_value] at hg
  have hi := PSTRTMThresholdDepthSource184.original_gap_le risk depth hr
  have hw := PSTRTMThresholdDepthSource184.original_bound_bits_le risk depth hr
  exact arithmetic_gap _ _ _ _ _ hg hi hw

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRiskReturnBudget230
