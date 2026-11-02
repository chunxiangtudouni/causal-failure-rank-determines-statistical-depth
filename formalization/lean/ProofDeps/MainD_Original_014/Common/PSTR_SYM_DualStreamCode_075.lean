module

public import Common.PSTR_SYM_NativeRemaining_074
public import Common.PSTR_SYM_PlannerFirstStream_070
public import Common.PSTR_TM_L01_RecordGate_251c

/-! ONE fixed finite code table for the two real encoded streams. Every
callee terminal is replaced by an actual WRITE-current-symbol edge to a
fixed or genuinely read finite port. Run/whole-output assembly follows;
this code declaration alone is not a complete parser/planner proof. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream

open Turing PSTRTMSeq005 PSTRSymbolicRawLoop PSTRSymbolicRawBootstrap
open PSTRSymbolicRetainedBootstrap PSTRSymbolicCursorCode PSTRTML01RecordGate251

inductive Label where
  | first : Fin (loopSupport.card + 1) → Label
  | guard : Fin 3 → Label
  | gate : Fin 5 → Label
  | boot : Fin (bootSupport.card + 1) → Label
  | remaining : Fin (loopSupport.card + 1) → Label
  | halt : Bool → Label
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.first 0⟩

def gateFinish (point : Fin 5) : Label :=
  if point.val = 3 then .halt true else .boot 0

noncomputable def dualCode : TM0.Machine Bool Label
  | .first q, bit => calledCode rawLoopMachine .first (fun _ => .guard 0) q bit
  | .guard q, bit => calledCode secondGuardMachine .guard (fun _ => .gate 0) q bit
  | .gate q, bit => calledCode gateMachine .gate gateFinish q bit
  | .boot q, bit => calledCode bootstrapMachine .boot (fun _ => .remaining PSTRSymbolicNativeRemaining.entryLabel) q bit
  | .remaining q, bit => calledCode rawLoopMachine .remaining (fun _ => .halt false) q bit
  | .halt _, _ => none

theorem first_return (final : MachineState loopSupport.card) (halt : TM0.step rawLoopMachine final = none) :
    TM0.step dualCode (tagCfg Label.first final) = some ⟨.guard 0,final.Tape⟩ :=
  called_step_none dualCode rawLoopMachine Label.first (fun _ => .guard 0) (by intro q bit; rfl) final halt

theorem guard_return (final : MachineState 2) (halt : TM0.step secondGuardMachine final = none) :
    TM0.step dualCode (tagCfg Label.guard final) = some ⟨.gate 0,final.Tape⟩ :=
  called_step_none dualCode secondGuardMachine Label.guard (fun _ => .gate 0) (by intro q bit; rfl) final halt

theorem gate_return (final : MachineState 4) (halt : TM0.step gateMachine final = none) :
    TM0.step dualCode (tagCfg Label.gate final) = some ⟨gateFinish final.q,final.Tape⟩ :=
  called_step_none dualCode gateMachine Label.gate gateFinish (by intro q bit; rfl) final halt

theorem gate_zero : gateFinish 3 = .halt true := rfl

theorem gate_positive : gateFinish 4 = .boot 0 := rfl

theorem boot_return (final : MachineState bootSupport.card) (halt : TM0.step bootstrapMachine final = none) :
    TM0.step dualCode (tagCfg Label.boot final) = some ⟨.remaining PSTRSymbolicNativeRemaining.entryLabel,final.Tape⟩ :=
  called_step_none dualCode bootstrapMachine Label.boot (fun _ => .remaining PSTRSymbolicNativeRemaining.entryLabel)
    (by intro q bit; rfl) final halt

theorem remaining_return (final : MachineState loopSupport.card) (halt : TM0.step rawLoopMachine final = none) :
    TM0.step dualCode (tagCfg Label.remaining final) = some ⟨.halt false,final.Tape⟩ :=
  called_step_none dualCode rawLoopMachine Label.remaining (fun _ => .halt false) (by intro q bit; rfl) final halt

theorem terminal (zero : Bool) (tape : Tape Bool) : TM0.step dualCode ⟨.halt zero,tape⟩ = none := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream
