module

public import Common.PSTR_SYM_NaturalDatum_032

/-! The real leading Datum bit chooses one of two fixed field parsers.
The transfer is a charged WRITE-current-symbol, retaining the complete Tape.
An EOF TRUE is NOT licensed as a Rat: the caller still needs a real Datum. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDatumParser

open Turing PSTRTMSeq005 PA17TMRatArithmeticParse002

def natLabel (label : Fin 19) : Fin 66 := ⟨1 + label.val, by omega⟩
def ratLabel (label : Fin 46) : Fin 66 := ⟨20 + label.val, by omega⟩
def natCfg (cfg : MachineState 18) : MachineState 65 := ⟨natLabel cfg.q, cfg.Tape⟩
def ratCfg (cfg : MachineState 45) : MachineState 65 := ⟨ratLabel cfg.q, cfg.Tape⟩
def datumState (label : Fin 66) (left right : List Bool) : MachineState 65 :=
  ⟨label, Tape.mk₂ left right⟩

def datumMachine : Machine 65 := fun label symbol =>
  if initial : label.val = 0 then
    some ((if symbol then ratLabel 0 else natLabel 0), .write symbol)
  else if isNat : label.val < 20 then
    (naturalDatumMachine ⟨label.val - 1, by omega⟩ symbol).map
      (fun (next, op) => (natLabel next, op))
  else
    (ratMachine ⟨label.val - 20, by omega⟩ symbol).map
      (fun (next, op) => (ratLabel next, op))

theorem datum_step_nat (cfg : MachineState 18) :
    TM0.step datumMachine (natCfg cfg) = (TM0.step naturalDatumMachine cfg).map natCfg := by
  cases cfg with
  | mk label tape =>
    unfold TM0.step datumMachine natCfg natLabel
    simp only [show ¬1 + label.val = 0 by omega, ↓reduceDIte,
      show 1 + label.val < 20 by omega, Nat.add_sub_cancel_left, Fin.eta]
    cases action : naturalDatumMachine label tape.head with
    | none => simp
    | some pair =>
      obtain ⟨next, op⟩ := pair
      cases op <;> simp

theorem datum_step_rat (cfg : MachineState 45) :
    TM0.step datumMachine (ratCfg cfg) = (TM0.step ratMachine cfg).map ratCfg := by
  cases cfg with
  | mk label tape =>
    unfold TM0.step datumMachine ratCfg ratLabel
    simp only [show ¬20 + label.val = 0 by omega, ↓reduceDIte,
      show ¬20 + label.val < 20 by omega, Nat.add_sub_cancel_left, Fin.eta]
    cases action : ratMachine label tape.head with
    | none => simp
    | some pair =>
      obtain ⟨next, op⟩ := pair
      cases op <;> simp

theorem datum_false_step (left right : List Bool) :
    TM0.step datumMachine (datumState 0 left (false :: right)) =
      some (natCfg ⟨0, Tape.mk₂ left (false :: right)⟩) := by
  simp [TM0.step, datumMachine, datumState, natCfg, natLabel, Tape.mk₂]

theorem datum_true_step (left right : List Bool) :
    TM0.step datumMachine (datumState 0 left (true :: right)) =
      some (ratCfg ⟨0, Tape.mk₂ left (true :: right)⟩) := by
  simp [TM0.step, datumMachine, datumState, ratCfg, ratLabel, Tape.mk₂]

theorem datum_nat_runsFrom (left right : List Bool) (trace : List (MachineState 18))
    (final : MachineState 18)
    (actual : RunsFrom naturalDatumMachine ⟨0, Tape.mk₂ left (false :: right)⟩ trace final) :
    RunsFrom datumMachine (datumState 0 left (false :: right))
      ([datumState 0 left (false :: right)] ++ trace.map natCfg) (natCfg final) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply List.IsChain.append
    · exact .singleton _
    · apply (List.isChain_map _).mpr
      exact actual.2.1.imp (fun before after step => by simp [datum_step_nat, step])
    · intro before beforeLast after afterHead
      simp only [List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      simp only [List.head?_map, actual.1, Option.map_some, Option.mem_some_iff] at afterHead
      subst before
      subst after
      exact datum_false_step left right
  · simp only [List.getLast?_append, List.getLast?_map, actual.2.2.1, Option.map_some, Option.some_or]
  · simp only [datum_step_nat, actual.2.2.2, Option.map_none]

theorem datum_rat_runsFrom (left right : List Bool) (trace : List (MachineState 45))
    (final : MachineState 45)
    (actual : RunsFrom ratMachine ⟨0, Tape.mk₂ left (true :: right)⟩ trace final) :
    RunsFrom datumMachine (datumState 0 left (true :: right))
      ([datumState 0 left (true :: right)] ++ trace.map ratCfg) (ratCfg final) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply List.IsChain.append
    · exact .singleton _
    · apply (List.isChain_map _).mpr
      exact actual.2.1.imp (fun before after step => by simp [datum_step_rat, step])
    · intro before beforeLast after afterHead
      simp only [List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      simp only [List.head?_map, actual.1, Option.map_some, Option.mem_some_iff] at afterHead
      subst before
      subst after
      exact datum_true_step left right
  · simp only [List.getLast?_append, List.getLast?_map, actual.2.2.1, Option.map_some, Option.some_or]
  · simp only [datum_step_rat, actual.2.2.2, Option.map_none]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDatumParser
