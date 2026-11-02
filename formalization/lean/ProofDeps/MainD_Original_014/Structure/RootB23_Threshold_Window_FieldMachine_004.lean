module

public import Structure.RootB23_Threshold_Window_FieldControl_003

@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

open Turing PSTRTMSeq005 PA17TMDivisionCompose006

abbrev fieldCap (states : Nat) : Nat := totalStates 3 (states + 12)

def fieldFamily {states : Nat} (body : Machine states) (phase : Fin 4) : Machine (states + 12) :=
  if phase.val = 0 then padMachine (by omega : 12 ≤ states + 12) fieldControl
  else if phase.val = 1 then padMachine (by omega : states ≤ states + 12) body
  else padMachine (by omega : 4 ≤ states + 12) (gapHomeMachine true)

def fieldPorts {states : Nat} (exit : Fin (states + 1))
    (phase : Fin 4) (q : Fin (states + 12 + 1)) :
    Option (Fin 4 × Fin (states + 12 + 1)) :=
  if phase.val = 0 ∧ q.val = 5 then some (1, 0)
  else if phase.val = 0 ∧ q.val = 9 then some (2, 0)
  else if phase.val = 0 ∧ q.val = 7 then some (3, 0)
  else if phase.val = 1 ∧ q.val = exit.val then
    some (0, padLabel (by omega : 12 ≤ states + 12) (6 : Fin 13))
  else if phase.val = 2 ∧ q.val = 4 then
    some (0, padLabel (by omega : 12 ≤ states + 12) (10 : Fin 13))
  else none

def fieldMachine {states : Nat} (body : Machine states) (exit : Fin (states + 1)) :
    Machine (fieldCap states) := blockMachine (fieldFamily body) (fieldPorts exit)

def controlLift {states : Nat} (state : MachineState 12) : MachineState (fieldCap states) :=
  blockCfg (0 : Fin 4) (padCfg (by omega : 12 ≤ states + 12) state)

def bodyLift {states : Nat} (state : MachineState states) : MachineState (fieldCap states) :=
  blockCfg (1 : Fin 4) (padCfg (by omega : states ≤ states + 12) state)

def homeLift {states : Nat} (phase : Fin 4) (state : MachineState 4) : MachineState (fieldCap states) :=
  blockCfg phase (padCfg (by omega : 4 ≤ states + 12) state)

theorem control_lift_step {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (before after : MachineState 12) (step : TM0.step fieldControl before = some after) :
    TM0.step (fieldMachine body exit) (controlLift before) = some (controlLift after) := by
  unfold fieldMachine controlLift
  rw [block_step]
  simp only [fieldFamily, Fin.val_zero, ite_true]
  rw [pad_step, step]
  rfl

theorem control_lift_segment {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (first last : MachineState 12) (trace : List (MachineState 12))
    (actual : Segment fieldControl first trace last) :
    Segment (fieldMachine body exit) (controlLift first) (trace.map controlLift) (controlLift last) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.head?_map, actual.1, Option.map_some]
  · apply (List.isChain_map _).mpr
    exact actual.2.1.imp (fun a b h => control_lift_step body exit a b h)
  · simp only [List.getLast?_map, actual.2.2, Option.map_some]

theorem body_lift_segment {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (first last : MachineState states) (trace : List (MachineState states))
    (actual : RunsFrom body first trace last) :
    Segment (fieldMachine body exit) (bodyLift first) (trace.map bodyLift) (bodyLift last) := by
  have padded := pad_runsFrom (by omega : states ≤ states + 12) body _ _ _ actual
  have familyRun : RunsFrom (fieldFamily body (1 : Fin 4))
      (padCfg (by omega : states ≤ states + 12) first)
      (trace.map (padCfg (by omega : states ≤ states + 12)))
      (padCfg (by omega : states ≤ states + 12) last) := by
    simpa only [fieldFamily, Fin.val_one, one_ne_zero, ite_false, ite_true] using padded
  have lifted := block_segment (fieldFamily body) (fieldPorts exit) (1 : Fin 4) _ _ _ familyRun
  have mapped : trace.map bodyLift =
      (trace.map (padCfg (by omega : states ≤ states + 12))).map (blockCfg (1 : Fin 4)) := by
    rw [List.map_map]
    rfl
  rw [mapped]
  exact lifted

theorem home_lift_segment {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (phase : Fin 4) (phaseTwo : phase.val = 2 ∨ phase.val = 3)
    (first last : MachineState 4) (trace : List (MachineState 4))
    (actual : RunsFrom (gapHomeMachine true) first trace last) :
    Segment (fieldMachine body exit) (homeLift phase first) (trace.map (homeLift phase)) (homeLift phase last) := by
  have neitherZero : phase.val ≠ 0 := by omega
  have neitherOne : phase.val ≠ 1 := by omega
  have padded := pad_runsFrom (by omega : 4 ≤ states + 12) (gapHomeMachine true) _ _ _ actual
  have familyRun : RunsFrom (fieldFamily body phase)
      (padCfg (by omega : 4 ≤ states + 12) first)
      (trace.map (padCfg (by omega : 4 ≤ states + 12)))
      (padCfg (by omega : 4 ≤ states + 12) last) := by
    simpa only [fieldFamily, neitherZero, neitherOne, ite_false] using padded
  have lifted := block_segment (fieldFamily body) (fieldPorts exit) phase _ _ _ familyRun
  have mapped : trace.map (homeLift phase) =
      (trace.map (padCfg (by omega : 4 ≤ states + 12))).map (blockCfg phase) := by
    rw [List.map_map]
    rfl
  rw [mapped]
  exact lifted

theorem control_to_body {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (tape : Tape Bool) :
    TM0.step (fieldMachine body exit) (controlLift (⟨5, tape⟩ : MachineState 12)) =
      some (bodyLift (⟨0, tape⟩ : MachineState states)) := by
  have halted : TM0.step (fieldFamily body (0 : Fin 4))
      (padCfg (by omega : 12 ≤ states + 12) (⟨5, tape⟩ : MachineState 12)) = none := by
    change TM0.step (padMachine (by omega : 12 ≤ states + 12) fieldControl)
      (padCfg (by omega : 12 ≤ states + 12) (⟨5, tape⟩ : MachineState 12)) = none
    rw [pad_step]
    simp [TM0.step, fieldControl]
  have transfer := block_transfer (fieldFamily body) (fieldPorts exit) (0 : Fin 4)
    (padCfg (by omega : 12 ≤ states + 12) (⟨5, tape⟩ : MachineState 12)) (1, 0) halted
    (by simp [fieldPorts, padCfg, padLabel])
  simpa [fieldMachine, controlLift, bodyLift, padCfg, padLabel] using transfer

theorem body_to_return {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (tape : Tape Bool) (halted : TM0.step body (⟨exit, tape⟩ : MachineState states) = none) :
    TM0.step (fieldMachine body exit) (bodyLift (⟨exit, tape⟩ : MachineState states)) =
      some (controlLift (⟨6, tape⟩ : MachineState 12)) := by
  have haltedFamily : TM0.step (fieldFamily body (1 : Fin 4))
      (padCfg (by omega : states ≤ states + 12) (⟨exit, tape⟩ : MachineState states)) = none := by
    simp only [fieldFamily, Fin.val_one, one_ne_zero, ite_false, ite_true, pad_step, halted, Option.map_none]
  have transfer := block_transfer (fieldFamily body) (fieldPorts exit) (1 : Fin 4)
    (padCfg (by omega : states ≤ states + 12) (⟨exit, tape⟩ : MachineState states))
    (0, padLabel (by omega : 12 ≤ states + 12) (6 : Fin 13))
    haltedFamily (by simp [fieldPorts, padCfg, padLabel])
  simpa [fieldMachine, controlLift, bodyLift, padCfg, padLabel] using transfer

theorem control_to_home {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (phase : Fin 4) (q : Fin 13)
    (chosen : (phase = 2 ∧ q = 9) ∨ (phase = 3 ∧ q = 7)) (tape : Tape Bool) :
    TM0.step (fieldMachine body exit) (controlLift (⟨q, tape⟩ : MachineState 12)) =
      some (homeLift phase (⟨0, tape⟩ : MachineState 4)) := by
  have localHalt : TM0.step fieldControl (⟨q, tape⟩ : MachineState 12) = none := by
    rcases chosen with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [TM0.step, fieldControl]
  have halted : TM0.step (fieldFamily body (0 : Fin 4))
      (padCfg (by omega : 12 ≤ states + 12) (⟨q, tape⟩ : MachineState 12)) = none := by
    simp only [fieldFamily, Fin.val_zero, ite_true, pad_step, localHalt, Option.map_none]
  have port : fieldPorts exit (0 : Fin 4)
      (padLabel (by omega : 12 ≤ states + 12) q) = some (phase, 0) := by
    rcases chosen with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [fieldPorts, padLabel]
  have transfer := block_transfer (fieldFamily body) (fieldPorts exit) (0 : Fin 4)
    (padCfg (by omega : 12 ≤ states + 12) (⟨q, tape⟩ : MachineState 12)) (phase, 0) halted port
  simpa [fieldMachine, controlLift, homeLift, padCfg, padLabel] using transfer

theorem home_to_restore {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (tape : Tape Bool) :
    TM0.step (fieldMachine body exit) (homeLift 2 (⟨4, tape⟩ : MachineState 4)) =
      some (controlLift (⟨10, tape⟩ : MachineState 12)) := by
  have halted : TM0.step (fieldFamily body (2 : Fin 4))
      (padCfg (by omega : 4 ≤ states + 12) (⟨4, tape⟩ : MachineState 4)) = none := by
    change TM0.step (padMachine (by omega : 4 ≤ states + 12) (gapHomeMachine true))
      (padCfg (by omega : 4 ≤ states + 12) (⟨4, tape⟩ : MachineState 4)) = none
    rw [pad_step]
    simp [TM0.step, gapHomeMachine]
  have transfer := block_transfer (fieldFamily body) (fieldPorts exit) (2 : Fin 4)
    (padCfg (by omega : 4 ≤ states + 12) (⟨4, tape⟩ : MachineState 4))
    (0, padLabel (by omega : 12 ≤ states + 12) (10 : Fin 13)) halted
    (by simp [fieldPorts, padCfg, padLabel])
  simpa [fieldMachine, controlLift, homeLift, padCfg, padLabel] using transfer

theorem final_home_halt {states : Nat} (body : Machine states) (exit : Fin (states + 1))
    (tape : Tape Bool) :
    TM0.step (fieldMachine body exit) (homeLift 3 (⟨4, tape⟩ : MachineState 4)) = none := by
  apply block_halt (fieldFamily body) (fieldPorts exit) (3 : Fin 4)
    (padCfg (by omega : 4 ≤ states + 12) (⟨4, tape⟩ : MachineState 4))
  · change TM0.step (padMachine (by omega : 4 ≤ states + 12) (gapHomeMachine true))
      (padCfg (by omega : 4 ≤ states + 12) (⟨4, tape⟩ : MachineState 4)) = none
    rw [pad_step]
    simp [TM0.step, gapHomeMachine]
  · simp [fieldPorts, padCfg, padLabel]

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
