module
public import Common.PSTR_TM_ThresholdCounterReturn_175

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopZero176
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthLoopCode173 PSTRTMThresholdDepthLoopLift174
open PSTRTMThresholdCounterReturn175

/-- Different control labels at adjacent phase endpoints are joined by
an ACTUAL transition, in contrast to duplicate-configuration overlap132. -/
theorem append_chain (first second : List (MachineState 387)) (before after : MachineState 387)
    (hf : first.IsChain (fun a b => Turing.TM0.step loopMachine a=some b))
    (hs : second.IsChain (fun a b => Turing.TM0.step loopMachine a=some b))
    (hl : first.getLast?=some before) (hh : second.head?=some after)
    (ht : Turing.TM0.step loopMachine before=some after) :
    (first++second).IsChain (fun a b => Turing.TM0.step loopMachine a=some b) := by
  apply List.IsChain.append hf hs
  intro current hc next hn
  rw [hl] at hc
  rw [hh] at hn
  have hcurrent := Option.mem_some_iff.mp hc
  have hnext := Option.mem_some_iff.mp hn
  subst current
  subst next
  exact ht

def prefixPart (archive depth : List Bool) (value gap : Nat) : List (MachineState 387) :=
  (PSTRTMThresholdCountdownPrefix172.prefixTrace archive depth (PSTRTMNatValue017.rawPayload value) gap).map prefixCfg

def returnPart (archive depth : List Bool) (value gap : Nat) : List (MachineState 387) :=
  (returnTrace archive depth value gap).map zeroCfg

def zeroFinal (archive depth : List Bool) (value gap : Nat) : MachineState 387 :=
  final (returnFinal archive depth value gap).Tape

def zeroTrace (archive depth : List Bool) (value gap : Nat) : List (MachineState 387) :=
  (prefixPart archive depth value gap++returnPart archive depth value gap)++[zeroFinal archive depth value gap]

def initial (archive depth : List Bool) (value gap : Nat) : MachineState 387 :=
  prefixCfg ⟨0,Turing.Tape.mk₂ (PSTRTMThresholdDepthEntry171.initialLeft archive depth (gap+1))
    (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩

theorem zero_head (archive depth : List Bool) (value gap : Nat) (hp : true∈depth) :
    (zeroTrace archive depth value gap).head?=some (initial archive depth value gap) := by
  have h := (PSTRTMThresholdCountdownPrefix172.prefix_runsFrom archive depth (PSTRTMNatValue017.rawPayload value) gap hp).1
  simp only [zeroTrace,List.head?_append,prefixPart,List.head?_map,h,Option.map_some,Option.some_or,initial]

theorem zero_last (archive depth : List Bool) (value gap : Nat) :
    (zeroTrace archive depth value gap).getLast?=some (zeroFinal archive depth value gap) := by
  simp only [zeroTrace,List.getLast?_append,List.getLast?_singleton,Option.some_or]

theorem zero_chain (archive depth : List Bool) (value gap : Nat) (hp : true∈depth)
    (hv : PSTRTMIncrement009.valueDigits depth=1) :
    (zeroTrace archive depth value gap).IsChain
      (fun before after => Turing.TM0.step loopMachine before=some after) := by
  have hpr := PSTRTMThresholdCountdownPrefix172.prefix_runsFrom archive depth (PSTRTMNatValue017.rawPayload value) gap hp
  have hrt := return_runsFrom archive depth value gap
  have hpLast : (prefixPart archive depth value gap).getLast?=some
      (prefixCfg (PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap)) := by
    simpa only [prefixPart,List.getLast?_map,Option.map_some] using congrArg (Option.map prefixCfg) hpr.2.2.1
  have hrHead : (returnPart archive depth value gap).head?=some
      (zeroCfg ⟨0,(PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap).Tape⟩) := by
    simpa only [returnPart,List.head?_map,Option.map_some] using congrArg (Option.map zeroCfg) hrt.1
  have hrLast : (returnPart archive depth value gap).getLast?=some (zeroCfg (returnFinal archive depth value gap)) := by
    simpa only [returnPart,List.getLast?_map,Option.map_some] using congrArg (Option.map zeroCfg) hrt.2.2.1
  have hq := (PSTRTMThresholdCountdownPrefix172.prefix_final_label_zero_iff archive depth
    (PSTRTMNatValue017.rawPayload value) gap hp).mpr hv
  have hfirst : Turing.TM0.step loopMachine
      (prefixCfg (PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap))=
      some (zeroCfg ⟨0,(PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap).Tape⟩) := by
    have h := prefix_step (PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap)
    rw [hpr.2.2.2] at h
    rw [zeroCfg_zero]
    simpa only [prefixPort,hq,↓reduceIte] using h
  have hjoin := append_chain _ _ _ _ (prefix_chain _ hpr.2.1) (PSTRTMThresholdDepthLoopLift174.zero_chain _ hrt.2.1)
    hpLast hrHead hfirst
  have hjoinLast : (prefixPart archive depth value gap++returnPart archive depth value gap).getLast?=
      some (zeroCfg (returnFinal archive depth value gap)) := by
    simp only [List.getLast?_append,hrLast,Option.some_or]
  have hlast : Turing.TM0.step loopMachine (zeroCfg (returnFinal archive depth value gap))=
      some (zeroFinal archive depth value gap) := by
    have h := zero_step (returnFinal archive depth value gap)
    rw [hrt.2.2.2] at h
    exact h
  exact append_chain _ _ _ _ hjoin (.singleton _) hjoinLast rfl hlast

/-- The fixed388-label machine really follows the observed ZERO return
port, returns across the entire actual gap to B, and truly HALTs387.
This is one terminal iteration, not the full positive-depth loop claim. -/
theorem zero_runsFrom (archive depth : List Bool) (value gap : Nat) (hp : true∈depth)
    (hv : PSTRTMIncrement009.valueDigits depth=1) :
    PSTRTMSeq005.RunsFrom loopMachine (initial archive depth value gap)
      (zeroTrace archive depth value gap) (zeroFinal archive depth value gap) :=
  ⟨zero_head _ _ _ _ hp,zero_chain _ _ _ _ hp hv,zero_last _ _ _ _,loop_halt _⟩

theorem zero_final_tape (archive depth : List Bool) (value gap : Nat) :
    (zeroFinal archive depth value gap).Tape=Turing.Tape.mk₂
      (PSTRTMThresholdDepthEntry171.initialLeft archive (PSTRTMThresholdCountdownCode164.predDigits depth) (gap+1))
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value)) := return_final_tape _ _ _ _

theorem zero_length_le (archive depth : List Bool) (value gap : Nat) (hp : true∈depth) :
    (zeroTrace archive depth value gap).length≤4*gap+9*depth.length+19 := by
  have hpTime := PSTRTMThresholdCountdownPrefix172.prefix_length_le archive depth (PSTRTMNatValue017.rawPayload value) gap hp
  have hrTime := return_length archive depth value gap
  simp only [zeroTrace,prefixPart,returnPart,List.length_append,List.length_map,List.length_singleton]
  omega

theorem zero_visitedSpace_le (archive depth : List Bool) (value gap : Nat) (hp : true∈depth) :
    visitedSpace loopMachine (archive.length+1+2*depth.length+2*(gap+1)+2*natBits value)
      (zeroTrace archive depth value gap)≤archive.length+2*natBits value+10*gap+20*depth.length+42 := by
  have ht := zero_length_le archive depth value gap hp
  have hs := PSTRTMTrace002.visitedSpace_le loopMachine
    (archive.length+1+2*depth.length+2*(gap+1)+2*natBits value) (zeroTrace archive depth value gap)
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopZero176
