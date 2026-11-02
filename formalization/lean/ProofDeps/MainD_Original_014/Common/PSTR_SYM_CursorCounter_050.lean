module

public import Common.PSTR_SYM_CursorStages_049

/-! The actual root-to-counter part of the SAME048 table. Six real RIGHTs
enter the actual header rewind; the actual borrow/zero then ends on END00.
The physical root triple comes from an internal three-digit split which
the original positive-input header producer must still establish. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorCounter

open Turing PSTRTMSeq005 PSTRTMRawNat010 PSTRTMIncrement009
open PA17TMRatArithmeticParse002 PSTRSymbolicCarry PSTRSymbolicCounter
open PSTRSymbolicZeroTail PSTRSymbolicCursorPorts PSTRSymbolicCursorCode PSTRSymbolicCursorStages

def rootTape (base older suffix : List Bool) (first second third : Bool) : Tape Bool :=
  Tape.mk₂ (third :: (leftBlocks older ++ false :: base))
    (true :: second :: true :: first :: true :: false :: false :: suffix)

theorem root_six_tape (base digits older suffix : List Bool) (first second third : Bool)
    (shape : digits.reverse = first :: second :: third :: older) :
    (Tape.move .right)^[6] (rootTape base older suffix first second third) =
      Tape.mk₂ (false :: (leftBlocks digits.reverse ++ false :: base)) (false :: suffix) := by
  rw [rootTape, six_moves_tape, shape]
  simp [leftBlocks]

theorem actual_six_counter (carry : Fin 8) (base digits older suffix : List Bool)
    (first second third : Bool) (shape : digits.reverse = first :: second :: third :: older)
    (positive : true ∈ digits) :
    ∃ (trace : List (TM0.Cfg Bool Label)) (final : TM0.Cfg Bool Label),
      trace.head? = some ⟨.six (carryLabel (13 : Fin 20) carry),rootTape base older suffix first second third⟩ ∧
      trace.IsChain (fun before after => TM0.step machine before = some after) ∧
      trace.getLast? = some final ∧
      final.q = .borrow (carryLabel (counterRoundFinal base digits suffix).q carry) ∧
      final.Tape = Tape.mk₂
        (leftBlocks (PSTRTMThresholdCountdownCode164.predDigits digits).reverse ++ false :: base)
        (false :: false :: suffix) ∧
      TM0.step machine final = some
        ⟨.one (decide ((counterRoundFinal base digits suffix).q.val = 15))
          (carryLabel (18 : Fin 20) carry),final.Tape⟩ ∧
      trace.length ≤ 10 * digits.length + 20 := by
  let initialTape := rootTape base older suffix first second third
  let headerTape := Tape.mk₂ (false :: (leftBlocks digits.reverse ++ false :: base)) (false :: suffix)
  let countEntry := (⟨0,Tape.mk₂ (false :: base) (blocks digits ++ false :: false :: suffix)⟩ : MachineState 16)
  let sixTrace := (rightSixTrace initialTape).map (carryCfg carry)
  let sixEnd := carryCfg carry (rightState 19 (by decide) headerTape)
  let rewindTrace := (fieldBackTrace base digits (false :: suffix)).map (carryCfg carry)
  let rewindEnd := carryCfg carry (fieldBackFinal base digits (false :: suffix))
  let countTrace := (counterRoundTrace base digits suffix).map (carryCfg carry)
  let countEnd := carryCfg carry (counterRoundFinal base digits suffix)
  have moved := right_six_runsFrom initialTape
  have physical : (Tape.move .right)^[6] initialTape = headerTape :=
    root_six_tape base digits older suffix first second third shape
  rw [physical] at moved
  have movedCarried := carry_runsFrom right19Machine carry _ _ _ moved
  have rewound := carried_field_back carry base digits (false :: suffix)
  have counted := carried_counter_round carry base digits suffix positive
  let sixFinish : Fin 160 → Label := fun current =>
    .rewind (carryLabel (0 : Fin 6) (savedLabel (states := 19) current))
  let rewindFinish : Fin 48 → Label := fun current =>
    .borrow (carryLabel (0 : Fin 17) (savedLabel (states := 5) current))
  let countFinish : Fin 136 → Label := fun current =>
    .one (decide ((originalLabel (states := 16) current).val = 15))
      (carryLabel (18 : Fin 20) (savedLabel (states := 16) current))
  have sixPart := called_endpoints machine (carryMachine right19Machine) Label.six sixFinish
    (by intro q bit; rfl) _ _ _ movedCarried
  have rewindPart := called_endpoints machine (carryMachine fieldBackMachine) Label.rewind rewindFinish
    (by intro q bit; rfl) _ _ _ rewound
  have countPart := called_endpoints machine (carryMachine counterRoundMachine) Label.borrow countFinish
    (by intro q bit; rfl) _ _ _ counted
  have sixHead : (sixTrace.map (tagCfg Label.six)).head? = some
      (tagCfg Label.six (carryCfg carry (rightState 13 (by decide) initialTape))) := sixPart.1
  have rewindLast : (rewindTrace.map (tagCfg Label.rewind)).getLast? =
      some (tagCfg Label.rewind rewindEnd) := rewindPart.2.2.1
  have countLast : (countTrace.map (tagCfg Label.borrow)).getLast? =
      some (tagCfg Label.borrow countEnd) := countPart.2.2.1
  have firstBridge : TM0.step machine (tagCfg Label.six sixEnd) = some
      (tagCfg Label.rewind (carryCfg carry (⟨0,headerTape⟩ : MachineState 5))) := by
    have edge := sixPart.2.2.2.1
    change TM0.step machine (tagCfg Label.six sixEnd) =
      some ⟨.rewind (carryLabel (0 : Fin 6) (savedLabel (carryLabel (19 : Fin 20) carry))),headerTape⟩ at edge
    rw [saved_carry] at edge
    exact edge
  have secondBridge : TM0.step machine (tagCfg Label.rewind rewindEnd) = some
      (tagCfg Label.borrow (carryCfg carry countEntry)) := by
    have edge := rewindPart.2.2.2.1
    change TM0.step machine (tagCfg Label.rewind rewindEnd) =
      some ⟨.borrow (carryLabel (0 : Fin 17)
        (savedLabel (carryLabel (fieldBackFinal base digits (false :: suffix)).q carry))),
          (fieldBackFinal base digits (false :: suffix)).Tape⟩ at edge
    rw [saved_carry] at edge
    exact edge
  let firstTrace := sixTrace.map (tagCfg Label.six) ++ rewindTrace.map (tagCfg Label.rewind)
  have firstChain : firstTrace.IsChain (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append sixPart.2.1 rewindPart.2.1
    intro before beforeLast after afterHead
    simp only [sixPart.2.2.1, Option.mem_some_iff] at beforeLast
    simp only [rewindPart.1, Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact firstBridge
  have firstLast : firstTrace.getLast? = some (tagCfg Label.rewind rewindEnd) := by
    simp only [firstTrace, List.getLast?_append, rewindLast, Option.some_or]
  let trace := firstTrace ++ countTrace.map (tagCfg Label.borrow)
  let final := tagCfg Label.borrow countEnd
  have chain : trace.IsChain (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append firstChain countPart.2.1
    intro before beforeLast after afterHead
    simp only [firstLast, Option.mem_some_iff] at beforeLast
    simp only [countPart.1, Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact secondBridge
  have returnStep : TM0.step machine final = some
      ⟨.one (decide ((counterRoundFinal base digits suffix).q.val = 15))
        (carryLabel (18 : Fin 20) carry),final.Tape⟩ := by
    have edge := countPart.2.2.2.1
    change TM0.step machine final = some
      ⟨.one (decide ((originalLabel (carryLabel (counterRoundFinal base digits suffix).q carry)).val = 15))
        (carryLabel (18 : Fin 20) (savedLabel (carryLabel (counterRoundFinal base digits suffix).q carry))),final.Tape⟩ at edge
    rw [original_carry, saved_carry] at edge
    exact edge
  refine ⟨trace, final, ?_, chain, ?_, rfl, carried_counter_end_tape carry base digits suffix, returnStep, ?_⟩
  · change trace.head? = some (tagCfg Label.six
      (carryCfg carry (rightState 13 (by decide) initialTape)))
    simp only [trace, firstTrace, List.head?_append, sixHead, Option.some_or]
  · simp only [trace, List.getLast?_append, countLast, Option.some_or, final]
  · have count := counterRound_time_le base digits suffix positive
    simp only [trace, firstTrace, List.length_append, List.length_map, sixTrace, right_six_length,
      rewindTrace, fieldBackTrace_length, countTrace]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorCounter
