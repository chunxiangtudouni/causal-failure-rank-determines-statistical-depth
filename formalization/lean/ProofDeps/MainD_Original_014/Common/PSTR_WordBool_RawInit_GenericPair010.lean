module

public import Common.PSTR_WordBool_RawInit_RetainedHeader009
public import Common.PSTR_SYM_PairedDatum_040
public import Common.PSTR_SYM_LaneArchive_044

/-! The same finite219-state two-Datum parser handles BOTH original tags
at BOTH positions. Original bytes, not a supplied parsed pair, are its
input. The actual archive suffix and arbitrary unread footer/tail remain
in one whole tape. This produces the internal room needed by the existing
large-count cursor; no Natural-first-two qualification is introduced. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005 PSTRSymbolicPairedArchive PSTRSymbolicLaneArchive

def pairedTwoMachine : Machine 219 := seqMachine datumCompactMachine datumCompactMachine

theorem actual_two_datums (archive : List Bool) (first second : Datum) (suffix : List Bool) :
    ∃ (trace : List (MachineState 219)) (final : MachineState 219),
      RunsFrom pairedTwoMachine
        ⟨0,Tape.mk₂ archive (encodeDatum first ++ encodeDatum second ++ suffix)⟩ trace final ∧
      final.Tape = Tape.mk₂ ((pairedDatum second).reverse ++ (pairedDatum first).reverse ++ archive) suffix ∧
      trace.length ≤ 256 * ((encodeDatum first).length + (encodeDatum second).length + 1)^2 ∧
      ∀ inputLength clock, visitedSpace pairedTwoMachine inputLength (trace.take clock) ≤
        inputLength + 512 * ((encodeDatum first).length + (encodeDatum second).length + 1)^2 + 1 := by
  obtain ⟨firstTrace,firstFinal,firstRun,firstTape,firstTime,_firstSpace⟩ :=
    raw_datum_parse_compact archive first (encodeDatum second ++ suffix)
  obtain ⟨secondTrace,secondFinal,secondRun,secondTape,secondTime,_secondSpace⟩ :=
    raw_datum_parse_compact ((pairedDatum first).reverse ++ archive) second suffix
  have secondStart : RunsFrom datumCompactMachine ⟨0,firstFinal.Tape⟩ secondTrace secondFinal := by
    rw [firstTape]
    exact secondRun
  let trace := firstTrace.map (leftCfg (b := 109)) ++ secondTrace.map (rightCfg (a := 109))
  let final := rightCfg (a := 109) secondFinal
  have initial : leftCfg (b := 109)
      (⟨0,Tape.mk₂ archive (encodeDatum first ++ (encodeDatum second ++ suffix))⟩ : MachineState 109) =
      (⟨0,Tape.mk₂ archive (encodeDatum first ++ (encodeDatum second ++ suffix))⟩ : MachineState 219) := by
    simp [leftCfg, leftLabel]
  have joined := seq_runsFrom datumCompactMachine datumCompactMachine
    ⟨0,Tape.mk₂ archive (encodeDatum first ++ (encodeDatum second ++ suffix))⟩
    firstFinal secondFinal firstTrace secondTrace firstRun secondStart
  rw [initial] at joined
  have firstFits := Nat.pow_le_pow_left
    (show (encodeDatum first).length + 1 ≤ (encodeDatum first).length + (encodeDatum second).length + 1 by omega) 2
  have secondFits := Nat.pow_le_pow_left
    (show (encodeDatum second).length + 1 ≤ (encodeDatum first).length + (encodeDatum second).length + 1 by omega) 2
  have time : trace.length ≤ 256 * ((encodeDatum first).length + (encodeDatum second).length + 1)^2 := by
    simp only [trace, List.length_append, List.length_map]
    omega
  refine ⟨trace,final,?_,?_,time,?_⟩
  · simpa only [pairedTwoMachine, trace, final, List.append_assoc] using joined
  · change secondFinal.Tape = _
    simpa only [List.append_assoc] using secondTape
  · intro inputLength clock
    have space := PSTRTMTrace002.visitedSpace_le pairedTwoMachine inputLength (trace.take clock)
    have short : (trace.take clock).length ≤ trace.length := by
      simp only [List.length_take]
      exact Nat.min_le_right _ _
    omega

theorem datum_pairs_min_two (value : Datum) : 2 ≤ (datumPairs value).length := by
  cases value with
  | natural number =>
    have room : 1 ≤ (PSTRTMNatValue017.rawPayload number).length :=
      List.length_pos_iff.mpr (rawPayload_nonempty number)
    simp only [datumPairs, naturalPairs, falsePairs, List.length_append, List.length_map,
      List.length_cons, List.length_nil]
    omega
  | rational value =>
    have nonempty : PA17TMRatArithmeticParse002.denominatorDigits value ≠ [] :=
      rawPayload_nonempty value.den
    cases shape : PA17TMRatArithmeticParse002.denominatorDigits value with
    | nil => exact False.elim (nonempty shape)
    | cons first later =>
      simp only [datumPairs, shape, rationalPairs, falsePairs, List.length_append, List.length_map,
        List.length_cons, List.length_nil]
      omega

theorem two_datums_archive_room (first second : Datum) :
    4 ≤ (allDatumPairs [first,second]).length := by
  have firstRoom := datum_pairs_min_two first
  have secondRoom := datum_pairs_min_two second
  simp only [allDatumPairs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit
