module
public import Common.PSTR_TM_ThresholdDepthLoopNext_177

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopPositive178
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthLoopCode173 PSTRTMThresholdDepthLoopLift174
open PSTRTMThresholdCounterReturn175 PSTRTMThresholdDepthLoopNext177

def returnPart (archive depth : List Bool) (value gap : Nat) : List (MachineState 387) :=
  (returnTrace archive depth value gap).map positiveCfg

def nextPart (archive depth : List Bool) (value gap : Nat) : List (MachineState 387) :=
  (callTrace archive depth value gap).map nextCfg

def continuation (archive depth : List Bool) (value gap : Nat) : MachineState 387 :=
  PSTRTMThresholdDepthLoopZero176.initial archive (PSTRTMThresholdCountdownCode164.predDigits depth)
    (nextValue value) (nextGap value gap)

def positiveTrace (archive depth : List Bool) (value gap : Nat) : List (MachineState 387) :=
  ((PSTRTMThresholdDepthLoopZero176.prefixPart archive depth value gap++returnPart archive depth value gap)++
    nextPart archive depth value gap)++[continuation archive depth value gap]

theorem positive_head (archive depth : List Bool) (value gap : Nat) (hp : true∈depth) :
    (positiveTrace archive depth value gap).head?=some (PSTRTMThresholdDepthLoopZero176.initial archive depth value gap) := by
  have h := (PSTRTMThresholdCountdownPrefix172.prefix_runsFrom archive depth (PSTRTMNatValue017.rawPayload value) gap hp).1
  simp only [positiveTrace,List.head?_append,PSTRTMThresholdDepthLoopZero176.prefixPart,List.head?_map,
    h,Option.map_some,Option.some_or,PSTRTMThresholdDepthLoopZero176.initial]

theorem positive_last (archive depth : List Bool) (value gap : Nat) :
    (positiveTrace archive depth value gap).getLast?=some (continuation archive depth value gap) := by
  simp only [positiveTrace,List.getLast?_append,List.getLast?_singleton,Option.some_or]

/-- Every transfer below is a real head-preserving write. The two
different return ports preserve the observed positive result, and the
last actual transition reenters q0 on the genuine new physical layout. -/
theorem positive_chain (archive depth : List Bool) (value gap : Nat) (hp : true∈depth)
    (hv : PSTRTMIncrement009.valueDigits depth≠1) :
    (positiveTrace archive depth value gap).IsChain
      (fun before after => Turing.TM0.step loopMachine before=some after) := by
  have hpr := PSTRTMThresholdCountdownPrefix172.prefix_runsFrom archive depth (PSTRTMNatValue017.rawPayload value) gap hp
  have hrt := return_runsFrom archive depth value gap
  have hnx := call_runsFrom archive depth value gap
  have hpLast : (PSTRTMThresholdDepthLoopZero176.prefixPart archive depth value gap).getLast?=some
      (prefixCfg (PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap)) := by
    simpa only [PSTRTMThresholdDepthLoopZero176.prefixPart,List.getLast?_map,Option.map_some] using
      congrArg (Option.map prefixCfg) hpr.2.2.1
  have hrHead : (returnPart archive depth value gap).head?=some
      (positiveCfg ⟨0,(PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap).Tape⟩) := by
    simpa only [returnPart,List.head?_map,Option.map_some] using congrArg (Option.map positiveCfg) hrt.1
  have hrLast : (returnPart archive depth value gap).getLast?=some (positiveCfg (returnFinal archive depth value gap)) := by
    simpa only [returnPart,List.getLast?_map,Option.map_some] using congrArg (Option.map positiveCfg) hrt.2.2.1
  have hnHead : (nextPart archive depth value gap).head?=some (nextCfg ⟨0,(returnFinal archive depth value gap).Tape⟩) := by
    simpa only [nextPart,List.head?_map,Option.map_some] using congrArg (Option.map nextCfg) hnx.1
  have hnLast : (nextPart archive depth value gap).getLast?=some (nextCfg (callFinal archive depth value gap)) := by
    simpa only [nextPart,List.getLast?_map,Option.map_some] using congrArg (Option.map nextCfg) hnx.2.2.1
  have hq : (PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap).q.val≠21 := by
    intro h
    exact hv ((PSTRTMThresholdCountdownPrefix172.prefix_final_label_zero_iff archive depth
      (PSTRTMNatValue017.rawPayload value) gap hp).mp h)
  have hfirst : Turing.TM0.step loopMachine
      (prefixCfg (PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap))=
      some (positiveCfg ⟨0,(PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap).Tape⟩) := by
    have h := prefix_step (PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap)
    rw [hpr.2.2.2] at h
    rw [positiveCfg_zero]
    simpa only [prefixPort,hq,↓reduceIte] using h
  have hsecond : Turing.TM0.step loopMachine (positiveCfg (returnFinal archive depth value gap))=
      some (nextCfg ⟨0,(returnFinal archive depth value gap).Tape⟩) := by
    have h := positive_step (returnFinal archive depth value gap)
    rw [hrt.2.2.2] at h
    exact h
  have hthird : Turing.TM0.step loopMachine (nextCfg (callFinal archive depth value gap))=
      some (continuation archive depth value gap) := by
    have h := next_step (callFinal archive depth value gap)
    rw [hnx.2.2.2,call_final_tape] at h
    exact h
  have hpReturn := PSTRTMThresholdDepthLoopZero176.append_chain _ _ _ _
    (prefix_chain _ hpr.2.1) (PSTRTMThresholdDepthLoopLift174.positive_chain _ hrt.2.1) hpLast hrHead hfirst
  have hpReturnLast : (PSTRTMThresholdDepthLoopZero176.prefixPart archive depth value gap++returnPart archive depth value gap).getLast?=
      some (positiveCfg (returnFinal archive depth value gap)) := by
    simp only [List.getLast?_append,hrLast,Option.some_or]
  have hwhole := PSTRTMThresholdDepthLoopZero176.append_chain _ _ _ _ hpReturn (next_chain _ hnx.2.1)
    hpReturnLast hnHead hsecond
  have hwholeLast : ((PSTRTMThresholdDepthLoopZero176.prefixPart archive depth value gap++returnPart archive depth value gap)++
      nextPart archive depth value gap).getLast?=some (nextCfg (callFinal archive depth value gap)) := by
    simp only [List.getLast?_append,hnLast,Option.some_or]
  exact PSTRTMThresholdDepthLoopZero176.append_chain _ _ _ _ hwhole (.singleton _) hwholeLast rfl hthird

/-- The endpoint is a CONTINUATION at q0, not a HALT. It is joined to
the next actual prefix by identical-configuration overlap132 later. -/
theorem continuation_label (archive depth : List Bool) (value gap : Nat) :
    (continuation archive depth value gap).q=0 := rfl

theorem positive_length_le (archive depth : List Bool) (value gap : Nat) (hp : true∈depth) :
    (positiveTrace archive depth value gap).length≤4*gap+9*depth.length+19+8192*(natBits value+1)^2 := by
  have hpTime := PSTRTMThresholdCountdownPrefix172.prefix_length_le archive depth (PSTRTMNatValue017.rawPayload value) gap hp
  have hrTime := return_length archive depth value gap
  have hnTime := call_length_le archive depth value gap
  simp only [positiveTrace,PSTRTMThresholdDepthLoopZero176.prefixPart,returnPart,nextPart,
    List.length_append,List.length_map,List.length_singleton]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopPositive178
