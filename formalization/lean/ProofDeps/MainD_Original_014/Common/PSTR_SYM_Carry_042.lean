module

public import Common.PSTR_SYM_PairedMarker_041
public import Common.PSTR_SYM_Relabel_006

/-! One fixed code table carries three finite saved bits through a real
callee. The current physical label supplies its carrier; there is no
runtime choice of a machine. The frozen006 map-step and displacement
theorems supply the local simulation facts. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCarry

open Turing PSTRTMSeq005 PSTRSymbolicRelabel

def carryLabel {states : Nat} (label : Fin (states + 1)) (carry : Fin 8) : Fin (8 * states + 8) :=
  ⟨8 * label.val + carry.val, by omega⟩

def originalLabel {states : Nat} (label : Fin (8 * states + 8)) : Fin (states + 1) :=
  ⟨label.val / 8, by omega⟩

def savedLabel {states : Nat} (label : Fin (8 * states + 8)) : Fin 8 :=
  ⟨label.val % 8, by omega⟩

theorem original_carry {states : Nat} (label : Fin (states + 1)) (carry : Fin 8) :
    originalLabel (carryLabel label carry) = label := by
  apply Fin.ext
  simp only [originalLabel, carryLabel]
  omega

theorem saved_carry {states : Nat} (label : Fin (states + 1)) (carry : Fin 8) :
    savedLabel (carryLabel label carry) = carry := by
  apply Fin.ext
  simp only [savedLabel, carryLabel]
  omega

def carryCfg {states : Nat} (carry : Fin 8) (cfg : MachineState states) : MachineState (8 * states + 7) :=
  relabelCfg (fun label => carryLabel label carry) cfg

def carryMachine {states : Nat} (machine : Machine states) : Machine (8 * states + 7) :=
  fun label symbol =>
    relabelMachine machine (fun next => carryLabel next (savedLabel label)) originalLabel label symbol

theorem code_at {states : Nat} (machine : Machine states) (carry : Fin 8) (cfg : MachineState states) :
    TM0.step (carryMachine machine) (carryCfg carry cfg) =
      TM0.step (relabelMachine machine (fun label => carryLabel label carry) originalLabel)
        (carryCfg carry cfg) := by
  cases cfg
  simp only [TM0.step, carryMachine, carryCfg, relabelCfg, saved_carry]

theorem carry_step {states : Nat} (machine : Machine states) (carry : Fin 8) (cfg : MachineState states) :
    TM0.step (carryMachine machine) (carryCfg carry cfg) =
      (TM0.step machine cfg).map (carryCfg carry) := by
  rw [code_at]
  exact (relabel_step machine Set.univ (fun label => carryLabel label carry) originalLabel
    (by intro label _; exact original_carry label carry) cfg (Set.mem_univ _)).symm

theorem carry_runsFrom {states : Nat} (machine : Machine states) (carry : Fin 8)
    (entry final : MachineState states) (trace : List (MachineState states))
    (actual : RunsFrom machine entry trace final) :
    RunsFrom (carryMachine machine) (carryCfg carry entry) (trace.map (carryCfg carry))
      (carryCfg carry final) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [List.head?_map, actual.1, Option.map_some]
  · apply (List.isChain_map _).mpr
    exact actual.2.1.imp (fun before after step => by simp [carry_step, step])
  · simp only [List.getLast?_map, actual.2.2.1, Option.map_some]
  · simp only [carry_step, actual.2.2.2, Option.map_none]

theorem carry_tape {states : Nat} (carry : Fin 8) (cfg : MachineState states) :
    (carryCfg carry cfg).Tape = cfg.Tape := rfl

theorem carry_saved {states : Nat} (carry : Fin 8) (cfg : MachineState states) :
    savedLabel (carryCfg carry cfg).q = carry := saved_carry cfg.q carry

theorem carry_length {states : Nat} (carry : Fin 8) (trace : List (MachineState states)) :
    (trace.map (carryCfg carry)).length = trace.length := List.length_map _

theorem carry_displacement {states : Nat} (machine : Machine states) (carry : Fin 8)
    (cfg : MachineState states) :
    displacement (carryMachine machine) (carryCfg carry cfg) = displacement machine cfg := by
  calc
    _ = displacement (relabelMachine machine (fun label => carryLabel label carry) originalLabel)
        (carryCfg carry cfg) := by
      unfold displacement carryMachine carryCfg relabelCfg
      rw [saved_carry]
    _ = sourceDisplacement machine cfg :=
      relabel_displacement machine (fun label => carryLabel label carry) originalLabel cfg
        (original_carry cfg.q carry)
    _ = displacement machine cfg := by
      unfold sourceDisplacement displacement
      cases machine cfg.q cfg.Tape.head with
      | none => rfl
      | some action =>
        obtain ⟨next, instruction⟩ := action
        cases instruction with
        | write symbol => rfl
        | move direction => cases direction <;> rfl

theorem carry_space {states : Nat} (machine : Machine states) (carry : Fin 8)
    (inputLength : Nat) (trace : List (MachineState states)) :
    visitedSpace (carryMachine machine) inputLength (trace.map (carryCfg carry)) =
      visitedSpace machine inputLength trace := by
  have movements : (trace.map (carryCfg carry)).map (displacement (carryMachine machine)) =
      trace.map (displacement machine) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro cfg _
    exact carry_displacement machine carry cfg
  unfold visitedSpace
  rw [movements]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCarry
