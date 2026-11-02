module
public import Common.ROOT_TM_GCD_Dispatch_018

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDLift020
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006 ROOTTMGCDDispatch018

variable {s : Nat}
def lift (h : s ≤ 139) (phase : Fin 23) (old : MachineState s) : MachineState 3219 :=
  blockCfg phase (padCfg h old)

theorem phase_segment (h : s ≤ 139) (phase : Fin 23) (machine : Machine s)
    (hf : family phase=padMachine h machine)
    (first last : MachineState s) (trace : List (MachineState s))
    (run : PSTRTMSeq005.RunsFrom machine first trace last) :
    Segment residentGcdMachine (lift h phase first) (trace.map (lift h phase)) (lift h phase last) := by
  have hp:=pad_runsFrom h machine first last trace run
  rw [←hf] at hp
  have hb:=block_segment family ports phase _ _ _ hp
  unfold lift residentGcdMachine
  simpa only [List.map_map,Function.comp_def] using hb

theorem phase_transfer (h : s ≤ 139) (phase nextPhase : Fin 23) (machine : Machine s)
    (hf : family phase=padMachine h machine) (last : MachineState s)
    (halt : Turing.TM0.step machine last=none) (nextLabel : Fin 140)
    (port : ports phase (padLabel h last.q)=some (nextPhase,nextLabel)) :
    Turing.TM0.step residentGcdMachine (lift h phase last)=
      some (blockCfg nextPhase ⟨nextLabel,last.Tape⟩) := by
  have hp : Turing.TM0.step (family phase) (padCfg h last)=none := by
    rw [hf,pad_step,halt,Option.map_none]
  exact block_transfer family ports phase (padCfg h last) (nextPhase,nextLabel) hp port

theorem phase_halt (h : s ≤ 139) (phase : Fin 23) (machine : Machine s)
    (hf : family phase=padMachine h machine) (last : MachineState s)
    (halt : Turing.TM0.step machine last=none)
    (port : ports phase (padLabel h last.q)=none) :
    Turing.TM0.step residentGcdMachine (lift h phase last)=none := by
  have hp : Turing.TM0.step (family phase) (padCfg h last)=none := by
    rw [hf,pad_step,halt,Option.map_none]
  exact block_halt family ports phase (padCfg h last) hp port

theorem lift_tape (h : s ≤ 139) (phase : Fin 23) (state : MachineState s) :
    (lift h phase state).Tape=state.Tape := rfl

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDLift020
