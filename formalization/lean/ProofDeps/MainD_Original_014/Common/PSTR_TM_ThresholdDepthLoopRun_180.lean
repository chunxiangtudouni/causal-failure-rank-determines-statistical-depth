module
public import Common.PSTR_TM_ThresholdDepthLoopTrace_179

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopRun180
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthLoopCode173 PSTRTMThresholdDepthLoopTrace179
open PSTRTMThresholdDepthLoopNext177 PSTRTMOverlap132

/-- All positive fixed-width depth fields, including fields with
leading zeroes, follow one ACTUAL finite388-label machine to trueHALT.
No fuel, width, answer, numerical B bound or caller branch is an input.
The same trace preserves the ENTIRE decoded risk archive. -/
theorem loop_runsFrom (archive depth : List Bool) (value gap : Nat) (hp : true∈depth) :
    PSTRTMSeq005.RunsFrom loopMachine (PSTRTMThresholdDepthLoopZero176.initial archive depth value gap)
      (loopTrace archive depth value gap) (loopFinal archive depth value gap) := by
  by_cases hv : PSTRTMIncrement009.valueDigits depth=1
  · rw [loopTrace_zero archive depth value gap hp hv,loopFinal_zero archive depth value gap hp hv]
    exact PSTRTMThresholdDepthLoopZero176.zero_runsFrom archive depth value gap hp hv
  · have hpNext := pred_positive depth hp hv
    have hrec := loop_runsFrom archive (PSTRTMThresholdCountdownCode164.predDigits depth)
      (nextValue value) (nextGap value gap) hpNext
    have hpHead := PSTRTMThresholdDepthLoopPositive178.positive_head archive depth value gap hp
    have hpLast := PSTRTMThresholdDepthLoopPositive178.positive_last archive depth value gap
    have hpChain := PSTRTMThresholdDepthLoopPositive178.positive_chain archive depth value gap hp hv
    rw [loopTrace_step archive depth value gap hp hv,loopFinal_step archive depth value gap hp hv]
    exact ⟨glue_head _ _ _ _ hpHead hpLast hrec.1,
      glue_chain loopMachine _ _ _ hpChain hrec.2.1 hpLast hrec.1,
      glue_last _ _ _ hrec.2.2.1,hrec.2.2.2⟩
termination_by PSTRTMIncrement009.valueDigits depth
decreasing_by
  have h := PSTRTMThresholdCountdownCode164.pred_value depth hp
  omega

theorem loop_final_tape (archive depth : List Bool) (value gap : Nat) :
    (loopFinal archive depth value gap).Tape=Turing.Tape.mk₂
      (PSTRTMThresholdDepthEntry171.initialLeft archive (outcome depth value gap).depth
        ((outcome depth value gap).gap+1))
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (outcome depth value gap).value)) := rfl

theorem loop_final_label (archive depth : List Bool) (value gap : Nat) :
    (loopFinal archive depth value gap).q=387 := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopRun180
