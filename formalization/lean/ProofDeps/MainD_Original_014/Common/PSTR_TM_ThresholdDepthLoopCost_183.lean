module
public import Common.PSTR_TM_ThresholdDepthLoopBudget_182

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopCost183
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthLoopCode173 PSTRTMThresholdDepthLoopNext177
open PSTRTMThresholdDepthLoopTrace179 PSTRTMThresholdDepthLoopValue181
open PSTRTMThresholdDepthLoopBudget182

/-- Actual configurations of fixed388-label loop, including every
depth scan, gap crossing, Bnext arithmetic and control transfer. The
bound argument is a proof measure, eliminated by choosing max initialB2;
it is neither an original input field nor a machine parameter. -/
theorem loop_length_le (archive depth : List Bool) (value bound gap : Nat)
    (hp : true∈depth) (hv : value≤bound) (hb : 2≤bound) :
    (loopTrace archive depth value gap).length≤PSTRTMIncrement009.valueDigits depth*
      phaseBudget (natBits bound) depth.length gap (PSTRTMIncrement009.valueDigits depth) := by
  by_cases hone : PSTRTMIncrement009.valueDigits depth=1
  · rw [loopTrace_zero archive depth value gap hp hone,hone,Nat.one_mul]
    simpa only [hone] using zero_length_budget archive depth value bound gap hp
  · have hpNext := pred_positive depth hp hone
    have hrec := loop_length_le archive (PSTRTMThresholdCountdownCode164.predDigits depth)
      (nextValue value) bound (nextGap value gap) hpNext (nextValue_le_bound value bound hv hb) hb
    have hlen := PSTRTMThresholdCountdownCode164.pred_length depth
    rw [hlen] at hrec
    have hdepth := PSTRTMThresholdCountdownCode164.pred_value depth hp
    have hpotential := phaseBudget_decreases (natBits bound) depth.length gap (nextGap value gap)
      (PSTRTMIncrement009.valueDigits depth)
      (PSTRTMIncrement009.valueDigits (PSTRTMThresholdCountdownCode164.predDigits depth))
      (nextGap_le value bound gap hv hb) hdepth
    have htail := hrec.trans (Nat.mul_le_mul_left
      (PSTRTMIncrement009.valueDigits (PSTRTMThresholdCountdownCode164.predDigits depth)) hpotential)
    rw [loopTrace_step archive depth value gap hp hone]
    apply (PSTRTMOverlap132.glue_length_le _ _).trans
    exact recurse_cost _ _ _ _ _ hdepth (positive_length_budget archive depth value bound gap hp hv hb) htail
termination_by PSTRTMIncrement009.valueDigits depth
decreasing_by
  have h := PSTRTMThresholdCountdownCode164.pred_value depth hp
  omega

/-- Original visitedSpace applied to this SAME complete running trace;
all original archived cells are included in the initial charge. -/
theorem loop_visitedSpace_le (archive depth : List Bool) (value bound gap : Nat)
    (hp : true∈depth) (hv : value≤bound) (hb : 2≤bound) :
    visitedSpace loopMachine (archive.length+1+2*depth.length+2*(gap+1)+2*natBits value)
      (loopTrace archive depth value gap)≤
      archive.length+1+2*depth.length+2*(gap+1)+2*natBits value+
        2*(PSTRTMIncrement009.valueDigits depth*
          phaseBudget (natBits bound) depth.length gap (PSTRTMIncrement009.valueDigits depth))+1 := by
  have ht := loop_length_le archive depth value bound gap hp hv hb
  have hs := PSTRTMTrace002.visitedSpace_le loopMachine
    (archive.length+1+2*depth.length+2*(gap+1)+2*natBits value) (loopTrace archive depth value gap)
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopCost183
