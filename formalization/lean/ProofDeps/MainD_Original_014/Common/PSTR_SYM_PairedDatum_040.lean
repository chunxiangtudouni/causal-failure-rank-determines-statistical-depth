module

public import Common.PSTR_SYM_PairedRationalRun_039

/-! The original Rat parser followed by its actual fixed in-place compactor,
and one fixed tag dispatcher for both original Datum constructors. The
output is an internal paired archive with the same payload bits and cursor;
it is not a change to the original symbolic input/output encoding. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive

open Turing PSTRTMSeq005 PSTRTMRawNat010 PA17TMRatArithmeticParse002
open PSTRSymbolicLocator (rawPayload_length)

def rationalParseCompactMachine : Machine 77 := seqMachine ratMachine rationalCompactMachine

theorem raw_rational_parse_compact (archive : List Bool) (value : Rat) (suffix : List Bool) :
    ∃ (trace : List (MachineState 77)) (final : MachineState 77),
      RunsFrom rationalParseCompactMachine ⟨0,Tape.mk₂ archive (encodeDatum (.rational value) ++ suffix)⟩
        trace final ∧
      final.Tape = Tape.mk₂
        ((pairedRationalWord (sign value) (numeratorDigits value) (denominatorDigits value)).reverse ++ archive) suffix ∧
      trace.length ≤ 64 * (natBits value.num.natAbs + natBits value.den + 1)^2 ∧
      ∀ inputLength clock, visitedSpace rationalParseCompactMachine inputLength (trace.take clock) ≤
        inputLength + 128 * (natBits value.num.natAbs + natBits value.den + 1)^2 + 1 := by
  obtain ⟨last, earlier, shape⟩ := PSTRSymbolicZeroTail.count_reverse_cons value.den
  have reverseShape : denominatorDigits value = earlier.reverse ++ [last] := by
    simpa only [denominatorDigits, List.reverse_reverse, List.reverse_cons] using
      congrArg List.reverse shape
  have width : natBits value.den = earlier.length + 1 := by
    simpa only [List.length_reverse, rawPayload_length, List.length_cons] using congrArg List.length shape
  have next : RunsFrom rationalCompactMachine
      ⟨0,(ratFinal archive (sign value) (numeratorDigits value) (denominatorDigits value) suffix).Tape⟩
      (ratCompactTrace archive (sign value) (numeratorDigits value).reverse last earlier suffix)
      (ratArchiveFinal archive (sign value) (numeratorDigits value) (earlier.reverse ++ [last]) suffix) := by
    rw [rat_final_tape]
    change RunsFrom rationalCompactMachine
      (ratState 0 (false :: (leftBlocks (denominatorDigits value).reverse ++ false ::
        numParsedLeft archive (sign value) (numeratorDigits value).reverse)) suffix) _ _
    change (PSTRTMNatValue017.rawPayload value.den).reverse = last :: earlier at shape
    rw [show (denominatorDigits value).reverse = last :: earlier from shape]
    simpa only [List.reverse_reverse] using
      ratCompact_runsFrom archive (sign value) (numeratorDigits value).reverse last earlier suffix
  let trace :=
    (ratTrace archive (sign value) (numeratorDigits value) (denominatorDigits value) suffix).map
        (leftCfg (b := 31)) ++
      (ratCompactTrace archive (sign value) (numeratorDigits value).reverse last earlier suffix).map
        (rightCfg (a := 45))
  let final : MachineState 77 := rightCfg (a := 45)
    (ratArchiveFinal archive (sign value) (numeratorDigits value) (earlier.reverse ++ [last]) suffix)
  have actual : RunsFrom rationalParseCompactMachine
      ⟨0,Tape.mk₂ archive (encodeDatum (.rational value) ++ suffix)⟩ trace final :=
    seq_runsFrom ratMachine rationalCompactMachine _
      (ratFinal archive (sign value) (numeratorDigits value) (denominatorDigits value) suffix) _ _ _
      (encodeDatum_rat_runsFrom archive suffix value) next
  have compactClock :
      (ratCompactTrace archive (sign value) (numeratorDigits value).reverse last earlier suffix).length =
        8 * natBits value.num.natAbs + 5 * natBits value.den + 14 := by
    simp only [ratCompact_length, List.length_reverse, numeratorDigits, rawPayload_length]
    omega
  have total : trace.length ≤ 64 * (natBits value.num.natAbs + natBits value.den + 1)^2 := by
    simp only [trace, List.length_append, List.length_map]
    rw [ratTrace_length, compactClock]
    simp only [numeratorDigits, denominatorDigits, rawPayload_length]
    nlinarith [Nat.zero_le (natBits value.num.natAbs), Nat.zero_le (natBits value.den),
      Nat.zero_le ((natBits value.num.natAbs)^2), Nat.zero_le ((natBits value.den)^2),
      Nat.zero_le (natBits value.num.natAbs * natBits value.den)]
  refine ⟨trace, final, actual, ?_, total, ?_⟩
  · change (ratArchiveFinal archive (sign value) (numeratorDigits value) (earlier.reverse ++ [last]) suffix).Tape = _
    rw [← reverseShape]
    rfl
  · intro inputLength tick
    have cells := PSTRTMTrace002.visitedSpace_le rationalParseCompactMachine inputLength (trace.take tick)
    have takeLength : (trace.take tick).length ≤ trace.length := by
      simp only [List.length_take]
      omega
    omega

/-! One genuine tag-bit branch. It is the same finite program for every
Datum, not a host choice between separately selected programs. -/

def compactNatLabel (label : Fin 31) : Fin 110 := ⟨1 + label.val, by omega⟩
def compactRatLabel (label : Fin 78) : Fin 110 := ⟨32 + label.val, by omega⟩
def compactNatCfg (cfg : MachineState 30) : MachineState 109 := ⟨compactNatLabel cfg.q, cfg.Tape⟩
def compactRatCfg (cfg : MachineState 77) : MachineState 109 := ⟨compactRatLabel cfg.q, cfg.Tape⟩
def compactDatumState (label : Fin 110) (left right : List Bool) : MachineState 109 :=
  ⟨label,Tape.mk₂ left right⟩

def datumCompactMachine : Machine 109 := fun label symbol =>
  if initial : label.val = 0 then
    some ((if symbol then compactRatLabel 0 else compactNatLabel 0), .write symbol)
  else if isNat : label.val < 32 then
    (naturalParseCompactMachine ⟨label.val - 1, by omega⟩ symbol).map
      (fun (next, op) => (compactNatLabel next, op))
  else
    (rationalParseCompactMachine ⟨label.val - 32, by omega⟩ symbol).map
      (fun (next, op) => (compactRatLabel next, op))

theorem compact_step_nat (cfg : MachineState 30) :
    TM0.step datumCompactMachine (compactNatCfg cfg) =
      (TM0.step naturalParseCompactMachine cfg).map compactNatCfg := by
  cases cfg with
  | mk label tape =>
    unfold TM0.step datumCompactMachine compactNatCfg compactNatLabel
    simp only [show ¬1 + label.val = 0 by omega, ↓reduceDIte,
      show 1 + label.val < 32 by omega, Nat.add_sub_cancel_left, Fin.eta]
    cases action : naturalParseCompactMachine label tape.head with
    | none => simp
    | some pair =>
      obtain ⟨next, op⟩ := pair
      cases op <;> simp

theorem compact_step_rat (cfg : MachineState 77) :
    TM0.step datumCompactMachine (compactRatCfg cfg) =
      (TM0.step rationalParseCompactMachine cfg).map compactRatCfg := by
  cases cfg with
  | mk label tape =>
    unfold TM0.step datumCompactMachine compactRatCfg compactRatLabel
    simp only [show ¬32 + label.val = 0 by omega, ↓reduceDIte,
      show ¬32 + label.val < 32 by omega, Nat.add_sub_cancel_left, Fin.eta]
    cases action : rationalParseCompactMachine label tape.head with
    | none => simp
    | some pair =>
      obtain ⟨next, op⟩ := pair
      cases op <;> simp

theorem compact_false_step (left right : List Bool) :
    TM0.step datumCompactMachine (compactDatumState 0 left (false :: right)) =
      some (compactNatCfg ⟨0,Tape.mk₂ left (false :: right)⟩) := by
  simp [TM0.step, datumCompactMachine, compactDatumState, compactNatCfg, compactNatLabel, Tape.mk₂]

theorem compact_true_step (left right : List Bool) :
    TM0.step datumCompactMachine (compactDatumState 0 left (true :: right)) =
      some (compactRatCfg ⟨0,Tape.mk₂ left (true :: right)⟩) := by
  simp [TM0.step, datumCompactMachine, compactDatumState, compactRatCfg, compactRatLabel, Tape.mk₂]

theorem compact_nat_runsFrom (left right : List Bool) (trace : List (MachineState 30))
    (final : MachineState 30)
    (actual : RunsFrom naturalParseCompactMachine ⟨0,Tape.mk₂ left (false :: right)⟩ trace final) :
    RunsFrom datumCompactMachine (compactDatumState 0 left (false :: right))
      ([compactDatumState 0 left (false :: right)] ++ trace.map compactNatCfg) (compactNatCfg final) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply List.IsChain.append
    · exact .singleton _
    · apply (List.isChain_map _).mpr
      exact actual.2.1.imp (fun before after step => by simp [compact_step_nat, step])
    · intro before beforeLast after afterHead
      simp only [List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      simp only [List.head?_map, actual.1, Option.map_some, Option.mem_some_iff] at afterHead
      subst before
      subst after
      exact compact_false_step left right
  · simp only [List.getLast?_append, List.getLast?_map, actual.2.2.1, Option.map_some, Option.some_or]
  · simp only [compact_step_nat, actual.2.2.2, Option.map_none]

theorem compact_rat_runsFrom (left right : List Bool) (trace : List (MachineState 77))
    (final : MachineState 77)
    (actual : RunsFrom rationalParseCompactMachine ⟨0,Tape.mk₂ left (true :: right)⟩ trace final) :
    RunsFrom datumCompactMachine (compactDatumState 0 left (true :: right))
      ([compactDatumState 0 left (true :: right)] ++ trace.map compactRatCfg) (compactRatCfg final) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply List.IsChain.append
    · exact .singleton _
    · apply (List.isChain_map _).mpr
      exact actual.2.1.imp (fun before after step => by simp [compact_step_rat, step])
    · intro before beforeLast after afterHead
      simp only [List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      simp only [List.head?_map, actual.1, Option.map_some, Option.mem_some_iff] at afterHead
      subst before
      subst after
      exact compact_true_step left right
  · simp only [List.getLast?_append, List.getLast?_map, actual.2.2.1, Option.map_some, Option.some_or]
  · simp only [compact_step_rat, actual.2.2.2, Option.map_none]

def pairedDatum : Datum → List Bool
  | .natural number => naturalWord (PSTRTMNatValue017.rawPayload number)
  | .rational value => pairedRationalWord (sign value) (numeratorDigits value) (denominatorDigits value)

theorem raw_datum_parse_compact (archive : List Bool) (value : Datum) (suffix : List Bool) :
    ∃ (trace : List (MachineState 109)) (final : MachineState 109),
      RunsFrom datumCompactMachine ⟨0,Tape.mk₂ archive (encodeDatum value ++ suffix)⟩ trace final ∧
      final.Tape = Tape.mk₂ ((pairedDatum value).reverse ++ archive) suffix ∧
      trace.length ≤ 128 * ((encodeDatum value).length + 1)^2 ∧
      ∀ inputLength clock, visitedSpace datumCompactMachine inputLength (trace.take clock) ≤
        inputLength + 256 * ((encodeDatum value).length + 1)^2 + 1 := by
  have extend (trace : List (MachineState 109)) (final : MachineState 109)
      (actual : RunsFrom datumCompactMachine ⟨0,Tape.mk₂ archive (encodeDatum value ++ suffix)⟩ trace final)
      (tape : final.Tape = Tape.mk₂ ((pairedDatum value).reverse ++ archive) suffix)
      (time : trace.length ≤ 128 * ((encodeDatum value).length + 1)^2) :
      ∃ (trace : List (MachineState 109)) (final : MachineState 109),
        RunsFrom datumCompactMachine ⟨0,Tape.mk₂ archive (encodeDatum value ++ suffix)⟩ trace final ∧
        final.Tape = Tape.mk₂ ((pairedDatum value).reverse ++ archive) suffix ∧
        trace.length ≤ 128 * ((encodeDatum value).length + 1)^2 ∧
        ∀ inputLength clock, visitedSpace datumCompactMachine inputLength (trace.take clock) ≤
          inputLength + 256 * ((encodeDatum value).length + 1)^2 + 1 := by
    refine ⟨trace, final, actual, tape, time, ?_⟩
    intro inputLength tick
    have cells := PSTRTMTrace002.visitedSpace_le datumCompactMachine inputLength (trace.take tick)
    have takeLength : (trace.take tick).length ≤ trace.length := by
      simp only [List.length_take]
      omega
    omega
  cases value with
  | natural number =>
    obtain ⟨trace, final, actual, tape, clock, _⟩ := raw_natural_parse_compact archive number suffix
    apply extend ([compactDatumState 0 archive (encodeDatum (.natural number) ++ suffix)] ++
      trace.map compactNatCfg) (compactNatCfg final)
    · exact compact_nat_runsFrom archive (encodeNat number ++ suffix) trace final actual
    · exact tape
    · simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
        PSTRTMLength004.encodeDatum_natural_length]
      calc
        _ ≤ 1 + 32 * (natBits number + 1)^2 := Nat.add_le_add_left clock 1
        _ ≤ 128 * (2 * natBits number + 2 + 1)^2 := by
          nlinarith [Nat.zero_le (natBits number), Nat.zero_le ((natBits number)^2)]
  | rational value =>
    obtain ⟨trace, final, actual, tape, clock, _⟩ := raw_rational_parse_compact archive value suffix
    apply extend ([compactDatumState 0 archive (encodeDatum (.rational value) ++ suffix)] ++
      trace.map compactRatCfg) (compactRatCfg final)
    · exact compact_rat_runsFrom archive (encodeDatum (.rational value) ++ suffix).tail trace final actual
    · exact tape
    · simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
        PSTRTMLength004.encodeDatum_rational_length]
      calc
        _ ≤ 1 + 64 * (natBits value.num.natAbs + natBits value.den + 1)^2 := Nat.add_le_add_left clock 1
        _ ≤ 128 * (2 * (natBits value.num.natAbs + natBits value.den) + 4 + 1)^2 := by
          nlinarith [Nat.zero_le ((natBits value.num.natAbs)^2), Nat.zero_le ((natBits value.den)^2),
            Nat.zero_le (natBits value.num.natAbs * natBits value.den)]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive
