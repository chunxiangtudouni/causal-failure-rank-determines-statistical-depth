module
public import Common.PSTR_TM_ThresholdCountdownPrefix_172
public import Common.PSTR_TM_ThresholdNextFrame_162

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopCode173
open PaperProofs.Common.Native.RationalControllerComputation

/-- Fixed388 labels. Prefix23 actually decrements/reads depth and keeps
the result at real HALT21/22. TWO actual3-label rightward pair seekers
preserve that finite return-control bit. Zero reaches trueHALT387;
positive calls fixed358-label Bnext, then a charged write-self reenters
the depth prefix. Ordinary seq-to0 is deliberately not used to discard
the observed result. No Bool branch, width, fuel or answer is an input. -/
def loopMachine : Machine 387 := fun q symbol =>
  if h0 : q.val<23 then
    match PSTRTMThresholdCountdownPrefix172.prefixMachine ⟨q.val,h0⟩ symbol with
    | none => some (if q.val=21 then 23 else 26,.write symbol)
    | some (next,statement) => some (⟨next.val,by have hn := next.isLt; omega⟩,statement)
  else if h1 : q.val<26 then
    match PSTRTMThresholdCounterSeek169.seekMachine ⟨q.val-23,by omega⟩ symbol with
    | none => some (387,.write symbol)
    | some (next,statement) => some (⟨23+next.val,by have hn := next.isLt; omega⟩,statement)
  else if h2 : q.val<29 then
    match PSTRTMThresholdCounterSeek169.seekMachine ⟨q.val-26,by omega⟩ symbol with
    | none => some (29,.write symbol)
    | some (next,statement) => some (⟨26+next.val,by have hn := next.isLt; omega⟩,statement)
  else if h3 : q.val<387 then
    match PSTRTMThresholdNextFrame162.nextMachine ⟨q.val-29,by omega⟩ symbol with
    | none => some (0,.write symbol)
    | some (next,statement) => some (⟨29+next.val,by have hn := next.isLt; omega⟩,statement)
  else none

def prefixCfg (configuration : MachineState 22) : MachineState 387 :=
  ⟨⟨configuration.q.val,by have hq := configuration.q.isLt; omega⟩,configuration.Tape⟩

def zeroCfg (configuration : MachineState 2) : MachineState 387 :=
  ⟨⟨23+configuration.q.val,by have hq := configuration.q.isLt; omega⟩,configuration.Tape⟩

def positiveCfg (configuration : MachineState 2) : MachineState 387 :=
  ⟨⟨26+configuration.q.val,by have hq := configuration.q.isLt; omega⟩,configuration.Tape⟩

def nextCfg (configuration : MachineState 357) : MachineState 387 :=
  ⟨⟨29+configuration.q.val,by have hq := configuration.q.isLt; omega⟩,configuration.Tape⟩

def final (tape : Turing.Tape Bool) : MachineState 387 := ⟨387,tape⟩

theorem loop_halt (tape : Turing.Tape Bool) : Turing.TM0.step loopMachine (final tape)=none := by
  simp [Turing.TM0.step,loopMachine,final]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopCode173
