module

public import Structure.PA17_TM_Division_Loop_002f
public import Structure.PA17_TM_Division_Loop_002g
public import Structure.PA17_TM_Division_Compose_006a
public import Structure.PA17_TM_Division_Tape_005a

/-! The actual input-independent seventeen-phase finite control. Every port
is determined only by phase and the local machine's genuine HALT label.
No dividend, divisor, width, fuel, quotient or remainder enters the code. -/

@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
open PSTRTMBinaryAdd024 PSTRTMCompareCode054

def loopMachines (phase : Fin 17) : Machine 33 :=
  match phase.val with
  | 0 => PA17TMDivisionCompose006.padMachine (by decide : 20 ≤ 33) compareMachine
  | 1 => PA17TMDivisionCompose006.padMachine (by decide : 5 ≤ 33) PSTRTMColumnRewind067.rewindMachine
  | 2 => PA17TMDivisionCompose006.padMachine (by decide : 5 ≤ 33) PSTRTMColumnRewind067.rewindMachine
  | 3 => PA17TMDivisionCompose006.padMachine (by decide : 27 ≤ 33) sourceMachine
  | 4 => PA17TMDivisionCompose006.padMachine (by decide : 27 ≤ 33) sourceMachine
  | 5 => PA17TMDivisionCompose006.padMachine (by decide : 19 ≤ 33) PSTRTMShiftColumnCode065.shiftMachine
  | 6 => PA17TMDivisionCompose006.padMachine (by decide : 19 ≤ 33) PSTRTMShiftColumnCode065.shiftMachine
  | 7 => PA17TMDivisionCompose006.padMachine (by decide : 5 ≤ 33) PSTRTMColumnRewind067.rewindMachine
  | 8 => PA17TMDivisionCompose006.padMachine (by decide : 5 ≤ 33) PSTRTMColumnRewind067.rewindMachine
  | 9 => PA17TMDivisionCompose006.padMachine (by decide : 20 ≤ 33) compareMachine
  | 10 => PA17TMDivisionCompose006.padMachine (by decide : 5 ≤ 33) PSTRTMColumnRewind067.rewindMachine
  | 11 => PA17TMDivisionCompose006.padMachine (by decide : 5 ≤ 33) PSTRTMColumnRewind067.rewindMachine
  | 12 => PA17TMDivisionCompose006.padMachine (by decide : 33 ≤ 33) PA17TMDivisionSub001.residentSubMachine
  | 13 => PA17TMDivisionCompose006.padMachine (by decide : 33 ≤ 33) (commitMachine false)
  | 14 => PA17TMDivisionCompose006.padMachine (by decide : 33 ≤ 33) (commitMachine false)
  | 15 => PA17TMDivisionCompose006.padMachine (by decide : 33 ≤ 33) (commitMachine true)
  | _ => fun _ _ => none

def loopPorts (phase : Fin 17) (label : Fin 34) : Option (Fin 17 × Fin 34) :=
  match phase.val with
  | 0 => if label.val = 18 then some (1,0) else some (2,0)
  | 1 => some (3,0)
  | 2 => some (4,0)
  | 3 => if label.val = 26 then some (5,0) else if label.val = 27 then some (5,1) else some (16,0)
  | 4 => if label.val = 26 then some (6,0) else if label.val = 27 then some (6,1) else some (16,0)
  | 5 => some (7,0)
  | 6 => some (8,0)
  | 7 => some (13,0)
  | 8 => some (9,0)
  | 9 => if label.val = 19 then some (10,0) else some (11,0)
  | 10 => some (14,0)
  | 11 => some (12,0)
  | 12 => some (15,0)
  | 13 => if label.val = 26 then some (3,0) else some (16,0)
  | 14 => if label.val = 26 then some (4,0) else some (16,0)
  | 15 => if label.val = 26 then some (4,0) else some (16,0)
  | _ => none

def loopMachine : Machine 577 := PA17TMDivisionCompose006.blockMachine loopMachines loopPorts

def phaseCfg (phase : Fin 17) (label : Fin 34) (tape : Turing.Tape Bool) : MachineState 577 :=
  PA17TMDivisionCompose006.blockCfg phase ⟨label,tape⟩

def liftCfg {a : Nat} (phase : Fin 17) (h : a ≤ 33) (state : MachineState a) : MachineState 577 :=
  PA17TMDivisionCompose006.blockCfg phase (PA17TMDivisionCompose006.padCfg h state)

def liftTrace {a : Nat} (phase : Fin 17) (h : a ≤ 33) (trace : List (MachineState a)) : List (MachineState 577) :=
  trace.map (fun state => PA17TMDivisionCompose006.blockCfg phase (PA17TMDivisionCompose006.padCfg h state))

theorem lift_segment {a : Nat} (phase : Fin 17) (h : a ≤ 33) (machine : Machine a)
    (heq : loopMachines phase = PA17TMDivisionCompose006.padMachine h machine)
    (first last : MachineState a) (trace : List (MachineState a))
    (run : PSTRTMSeq005.RunsFrom machine first trace last) :
    PA17TMDivisionCompose006.Segment loopMachine (liftCfg phase h first) (liftTrace phase h trace) (liftCfg phase h last) := by
  have localRun := PA17TMDivisionCompose006.pad_runsFrom h machine first last trace run
  rw [← heq] at localRun
  have segment := PA17TMDivisionCompose006.block_segment loopMachines loopPorts phase _ _ _ localRun
  change PA17TMDivisionCompose006.Segment
    (PA17TMDivisionCompose006.blockMachine loopMachines loopPorts)
    (PA17TMDivisionCompose006.blockCfg phase (PA17TMDivisionCompose006.padCfg h first))
    (trace.map (fun state => PA17TMDivisionCompose006.blockCfg phase (PA17TMDivisionCompose006.padCfg h state)))
    (PA17TMDivisionCompose006.blockCfg phase (PA17TMDivisionCompose006.padCfg h last))
  simpa only [List.map_map,Function.comp_def] using segment

/-- Prepend one real component run and its charged HALT-port transition. -/
theorem prepend_component {a : Nat} (phase : Fin 17) (h : a ≤ 33) (machine : Machine a)
    (heq : loopMachines phase = PA17TMDivisionCompose006.padMachine h machine)
    (first last : MachineState a) (trace : List (MachineState a))
    (run : PSTRTMSeq005.RunsFrom machine first trace last)
    (targetPhase : Fin 17) (targetLabel : Fin 34)
    (port : loopPorts phase (PA17TMDivisionCompose006.padLabel h last.q) = some (targetPhase,targetLabel))
    (final : MachineState 577) (suffix : List (MachineState 577))
    (rest : PA17TMDivisionCompose006.Segment loopMachine (phaseCfg targetPhase targetLabel last.Tape) suffix final) :
    PA17TMDivisionCompose006.Segment loopMachine (liftCfg phase h first) (liftTrace phase h trace ++ suffix) final := by
  apply PA17TMDivisionCompose006.segment_append loopMachine _ _ _ final _ suffix (lift_segment phase h machine heq first last trace run) rest
  have localHalt : Turing.TM0.step (loopMachines phase) (PA17TMDivisionCompose006.padCfg h last) = none := by
    rw [heq, PA17TMDivisionCompose006.pad_step, run.2.2.2]
    rfl
  exact PA17TMDivisionCompose006.block_transfer loopMachines loopPorts phase (PA17TMDivisionCompose006.padCfg h last) (targetPhase,targetLabel) localHalt port

def readPhase (zeroMode : Bool) : Fin 17 := if zeroMode then 3 else 4

def archiveFor (remaining quotient : List Bool) : List (Bool × Bool) :=
  remaining.reverse.map (fun bit => (bit,true)) ++ quotient.map (fun bit => (bit,false))

def frameLeft (context : List Bool) (archive : List (Bool × Bool)) : List Bool :=
  false :: false :: false :: (leftColumns archive.reverse ++ false :: context)

def residentRight (resident : List (Bool × Bool)) (suffix : List Bool) : List Bool :=
  operandColumns resident ++ false :: false :: suffix

def loopTape (context : List Bool) (archive resident : List (Bool × Bool)) (suffix : List Bool) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (frameLeft context archive) (residentRight resident suffix)

/-- The explicit far-left false guard is only blank normalization; no
nonblank archive, resident cell, move or erase is discarded. -/
theorem loopTape_original_layout (archive resident : List (Bool × Bool)) :
    loopTape [] archive resident [] =
      Turing.Tape.mk₂ (false :: false :: false :: (operandColumns archive).reverse)
        (operandColumns resident ++ [false,false]) := by
  change Turing.Tape.mk₂ ((false :: false :: false :: leftColumns archive.reverse) ++ [false])
    (operandColumns resident ++ [false,false]) = _
  simp only [Turing.Tape.mk₂,PSTRTMRawNat010.blank_append_false,PA17TMDivisionTape005.leftColumns_reverse]

theorem scanMode_done_append (done : List Bool) (remaining : List (Bool × Bool)) :
    scanMode (done.map (fun bit => (bit,false)) ++ remaining) = scanMode remaining := by
  induction done with
  | nil => rfl
  | cons bit later ih => simpa only [List.map_cons,List.cons_append,scanMode] using ih

theorem commitMode_done_append (done : List Bool) (remaining : List (Bool × Bool)) :
    commitMode (done.map (fun bit => (bit,false)) ++ remaining) = commitMode remaining := by
  induction done with
  | nil => rfl
  | cons bit later ih => simpa only [List.map_cons,List.cons_append,commitMode] using ih

theorem commitMSB_done_append (emit : Bool) (done : List Bool) (remaining : List (Bool × Bool)) :
    commitMSB emit (done.map (fun bit => (bit,false)) ++ remaining) =
      done.map (fun bit => (bit,false)) ++ commitMSB emit remaining := by
  induction done with
  | nil => rfl
  | cons bit later ih => simpa only [List.map_cons,List.cons_append,commitMSB] using congrArg (List.cons (bit,false)) ih

theorem archiveFor_length (remaining quotient : List Bool) :
    (archiveFor remaining quotient).length = remaining.length + quotient.length := by
  simp only [archiveFor,List.length_append,List.length_map,List.length_reverse]

theorem archiveFor_reverse (remaining quotient : List Bool) :
    (archiveFor remaining quotient).reverse =
      quotient.reverse.map (fun bit => (bit,false)) ++ remaining.map (fun bit => (bit,true)) := by
  simp only [archiveFor,List.reverse_append,← List.map_reverse,List.reverse_reverse]

theorem archiveFor_read_none (quotient : List Bool) : scanMode (archiveFor [] quotient).reverse = 0 := by
  rw [archiveFor_reverse,scanMode_done_append]
  rfl

theorem archiveFor_read_bit (bit : Bool) (remaining quotient : List Bool) :
    scanMode (archiveFor (bit :: remaining) quotient).reverse = bitMode bit := by
  rw [archiveFor_reverse,scanMode_done_append]
  rfl

theorem archiveFor_commit_mode (bit : Bool) (remaining quotient : List Bool) :
    commitMode (archiveFor (bit :: remaining) quotient).reverse = 1 := by
  rw [archiveFor_reverse,commitMode_done_append]
  rfl

theorem archiveFor_commit (emit bit : Bool) (remaining quotient : List Bool) :
    commitMSB emit (archiveFor (bit :: remaining) quotient).reverse =
      (archiveFor remaining (emit :: quotient)).reverse := by
  rw [archiveFor_reverse,commitMSB_done_append,archiveFor_reverse]
  simp only [List.map_cons,commitMSB,List.reverse_cons,List.map_append,List.append_assoc,List.map_nil,List.nil_append,List.cons_append]

theorem done_segment (tape : Turing.Tape Bool) :
    PA17TMDivisionCompose006.Segment loopMachine (phaseCfg 16 0 tape) [phaseCfg 16 0 tape] (phaseCfg 16 0 tape) :=
  ⟨rfl,List.isChain_singleton _,rfl⟩

theorem done_halt (tape : Turing.Tape Bool) :
    Turing.TM0.step loopMachine (phaseCfg 16 0 tape) = none := by
  exact PA17TMDivisionCompose006.block_halt loopMachines loopPorts 16 ⟨0,tape⟩ rfl rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
