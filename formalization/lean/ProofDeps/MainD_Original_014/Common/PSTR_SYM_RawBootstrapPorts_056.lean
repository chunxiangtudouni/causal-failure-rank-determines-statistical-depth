module

public import Common.PSTR_SYM_RawBootstrapCode_055

/-! SOURCEONLY, not yet checked. Necessary physical ports for the raw
bootstrap. A counter's END00 is crossed by an actual RIGHT, and the real
Datum parsers retain the arbitrary original suffix. The whole raw entry
composition, its finite relabeling and original complexity remain open. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawBootstrap

open Turing PSTRTMSeq005 PSTRTMIncrement009 PSTRTMNatValue017 PSTRTMRawNat010
open PSTRTMThresholdCountdownCode164 PSTRSymbolicCounter PSTRSymbolicPairedArchive
open PA17TMRatArithmeticParse002 PSTRSymbolicLaneArchive

def afterTwo (count : Nat) : List Bool := predDigits (predDigits (rawPayload count))

theorem two_count_rounds (count : Nat) (room : 2 ≤ count) :
    true ∈ rawPayload count ∧ true ∈ predDigits (rawPayload count) ∧
      valueDigits (afterTwo count) + 2 = count ∧
      (afterTwo count).length = (rawPayload count).length := by
  have first : true ∈ rawPayload count := has_true_of_value_pos _ (by rw [valueDigits_rawPayload]; omega)
  have firstValue := pred_value (rawPayload count) first
  rw [valueDigits_rawPayload] at firstValue
  have second : true ∈ predDigits (rawPayload count) := has_true_of_value_pos _ (by omega)
  have secondValue := pred_value (predDigits (rawPayload count)) second
  refine ⟨first,second,?_,?_⟩
  · change valueDigits (predDigits (predDigits (rawPayload count))) + 2 = count
    omega
  · simp only [afterTwo,pred_length]

/-- Both FALSEs in END00 are real original/header cells. RIGHT moves to
the still-unparsed Natural tag and pushes END to the left archive. -/
theorem counter_end_right (base digits suffix : List Bool) :
    (Tape.mk₂ (leftBlocks digits.reverse ++ false :: base) (false :: false :: suffix)).move .right =
      Tape.mk₂ (false :: (leftBlocks digits.reverse ++ false :: base)) (false :: suffix) := by
  simp [Tape.mk₂]

theorem stage_tool_pair (archive suffix : List Bool) (stage tools : Nat) :
    ∃ (trace : List (MachineState 219)) (final : MachineState 219),
      RunsFrom pairMachine
        ⟨0,Tape.mk₂ archive (encodeDatum (.natural stage) ++ encodeDatum (.natural tools) ++ suffix)⟩ trace final ∧
      final.Tape = Tape.mk₂
        ((pairedDatum (.natural tools)).reverse ++ (pairedDatum (.natural stage)).reverse ++ archive) suffix ∧
      trace.length ≤ 128 * ((encodeDatum (.natural stage)).length + 1)^2 +
        128 * ((encodeDatum (.natural tools)).length + 1)^2 := by
  obtain ⟨stageTrace,stageFinal,stageActual,stageTape,stageTime,_⟩ :=
    raw_datum_parse_compact archive (.natural stage) (encodeDatum (.natural tools) ++ suffix)
  obtain ⟨toolTrace,toolFinal,toolActual,toolTape,toolTime,_⟩ :=
    raw_datum_parse_compact ((pairedDatum (.natural stage)).reverse ++ archive) (.natural tools) suffix
  have secondActual : RunsFrom datumCompactMachine ⟨0,stageFinal.Tape⟩ toolTrace toolFinal := by
    rw [stageTape]
    exact toolActual
  let trace := stageTrace.map (leftCfg (b := 109)) ++ toolTrace.map (rightCfg (a := 109))
  let final := rightCfg (a := 109) toolFinal
  have initial : leftCfg (b := 109)
      (⟨0,Tape.mk₂ archive (encodeDatum (.natural stage) ++ (encodeDatum (.natural tools) ++ suffix))⟩ : MachineState 109) =
      (⟨0,Tape.mk₂ archive (encodeDatum (.natural stage) ++ (encodeDatum (.natural tools) ++ suffix))⟩ : MachineState 219) := by
    simp [leftCfg,leftLabel]
  have actual := seq_runsFrom datumCompactMachine datumCompactMachine
    ⟨0,Tape.mk₂ archive (encodeDatum (.natural stage) ++ (encodeDatum (.natural tools) ++ suffix))⟩
    stageFinal toolFinal stageTrace toolTrace stageActual secondActual
  rw [initial] at actual
  refine ⟨trace,final,?_,?_,?_⟩
  · simpa only [pairMachine,trace,final,List.append_assoc] using actual
  · change toolFinal.Tape = _
    simpa only [List.append_assoc] using toolTape
  · simp only [trace,List.length_append,List.length_map]
    omega

theorem stage_tool_pairs_room (stage tools : Nat) :
    4 ≤ (allDatumPairs [.natural stage,.natural tools]).length := by
  have stageNonempty := PSTRSymbolicLaneArchive.rawPayload_nonempty stage
  have toolNonempty := PSTRSymbolicLaneArchive.rawPayload_nonempty tools
  have stageLength : 1 ≤ (rawPayload stage).length := List.length_pos_iff.mpr stageNonempty
  have toolLength : 1 ≤ (rawPayload tools).length := List.length_pos_iff.mpr toolNonempty
  simp only [allDatumPairs,List.flatMap_cons,List.flatMap_nil,datumPairs,naturalPairs,
    List.length_append,falsePairs,List.length_map,List.length_cons,List.length_nil]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawBootstrap
