module
public import Structure.PA17_TM_Division_Loop_002h
public import Structure.PA17_TM_Division_Compose_006a

/-! Real finite-control component ports. Every Hop includes the genuine
write-self transfer from a parent HALT to its next local entry singleton. -/
@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionKernelPort010
open PA17TMDivisionLoop002
open PSTRTMCompareCode054 (leftColumns)

def eofTape (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (leftColumns resident.reverse ++ frameLeft context archive) (false::false::suffix)

def rewindArchive (context : List Bool) (archive : List (Bool × Bool)) : List Bool :=
  false::false::(leftColumns archive.reverse ++ false::context)

def Hop (first last : MachineState 577) (length : Nat) : Prop :=
  ∃ trace, PA17TMDivisionCompose006.Segment loopMachine first trace last ∧ trace.length = length

theorem component_hop {a : Nat} (phase : Fin 17) (h : a ≤ 33) (machine : Machine a)
    (heq : loopMachines phase = PA17TMDivisionCompose006.padMachine h machine)
    (first last : MachineState a) (trace : List (MachineState a))
    (run : PSTRTMSeq005.RunsFrom machine first trace last) (targetPhase : Fin 17)
    (port : loopPorts phase (PA17TMDivisionCompose006.padLabel h last.q) = some (targetPhase,0)) :
    Hop (liftCfg phase h first) (phaseCfg targetPhase 0 last.Tape) (trace.length+1) := by
  refine ⟨liftTrace phase h trace ++ [phaseCfg targetPhase 0 last.Tape],?_,?_⟩
  · exact prepend_component phase h machine heq first last trace run targetPhase 0 port
      (phaseCfg targetPhase 0 last.Tape) [phaseCfg targetPhase 0 last.Tape]
      ⟨rfl,List.isChain_singleton _,rfl⟩
  · rw [List.length_append,List.length_singleton]
    change (trace.map (fun state => PA17TMDivisionCompose006.blockCfg phase
      (PA17TMDivisionCompose006.padCfg h state))).length + 1 = trace.length + 1
    exact congrArg (fun n : Nat => n+1) (List.length_map _)

def compare0Target (relation : Fin 3) : Fin 17 := if relation.val = 0 then 1 else 2
def compare9Target (relation : Fin 3) : Fin 17 := if relation.val = 1 then 10 else 11

def shiftLabel (bit : Bool) : Fin 34 := PA17TMDivisionCompose006.padLabel (by decide : 19 ≤ 33) (PSTRTMShiftColumnCode065.readA bit)

theorem shiftLabel_eq (bit : Bool) : shiftLabel bit = if bit then 1 else 0 := by cases bit <;> rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionKernelPort010
