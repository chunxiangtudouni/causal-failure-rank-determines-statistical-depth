module

public import Common.PSTR_WordBool_RawInit_CountedPair011

/-! A fixed finite machine for the original n>=2 front. The gate reads the
actual outer binary count and restores the whole tape; the counted pair
front then retains the original bits, performs two real decrements and
parses two arbitrary Datum tags. This is the large branch producer ABI;
small n branches remain separate in the final all-data assembler. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.Assembler

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005

def machine : Machine 750 := seqMachine countGateMachine countedPairMachine

theorem actual_large (first second : Datum) (remaining : List Datum) :
    ∃ trace final,
      Runs machine (encode (first :: second :: remaining)) trace final ∧
      final.Tape = Tape.mk₂
        (countedPairLeft first second remaining) (rawTail remaining) ∧
      trace.length ≤ 30000 * ((encode (first :: second :: remaining)).length + 1)^2 ∧
      ∀ clock, visitedSpace machine (encode (first :: second :: remaining)).length (trace.take clock) ≤
        30000 * ((encode (first :: second :: remaining)).length + 1)^2 := by
  obtain ⟨gateTrace,gateFinal,gateRun,gatePort,gateTape,gateTime,gateSpace⟩ :=
    actual_count_gate (first :: second :: remaining)
  obtain ⟨pairTrace,pairFinal,pairRun,pairTape,pairTime,pairSpace⟩ :=
    actual_counted_pair first second remaining
  have pairFrom : RunsFrom countedPairMachine ⟨0,gateFinal.Tape⟩ pairTrace pairFinal := by
    rw [gateTape]
    exact ⟨pairRun.1,pairRun.2.1,pairRun.2.2.1,pairRun.2.2.2.1⟩
  let trace := gateTrace.map (leftCfg (b := 725)) ++ pairTrace.map (rightCfg (a := 24))
  let final := rightCfg (a := 24) pairFinal
  have run := seq_runs countGateMachine countedPairMachine (encode (first :: second :: remaining))
    gateFinal pairFinal gateTrace pairTrace gateRun pairFrom
  refine ⟨trace,final,?_,?_,?_,?_⟩
  · simpa only [machine,trace,final] using run
  · change pairFinal.Tape = _
    exact pairTape
  · have traceLength : trace.length = gateTrace.length + pairTrace.length := by
      simp only [trace,List.length_append,List.length_map]
    have positiveSpace : 0 < ((encode (first :: second :: remaining)).length + 1)^2 := by positivity
    have traceBound : trace.length ≤ 10000 * ((encode (first :: second :: remaining)).length + 1)^2 := by
      rw [traceLength]
      omega
    exact traceBound.trans (by omega)
  · intro clock
    have space := PSTRTMTrace002.visitedSpace_le machine (encode (first :: second :: remaining)).length (trace.take clock)
    have short := List.length_take_le' clock trace
    have square : (encode (first :: second :: remaining)).length ≤
        ((encode (first :: second :: remaining)).length + 1)^2 := by nlinarith
    have positive : 0 < ((encode (first :: second :: remaining)).length + 1)^2 := by positivity
    have traceBound : trace.length ≤ 10000 * ((encode (first :: second :: remaining)).length + 1)^2 := by
      have traceLength : trace.length = gateTrace.length + pairTrace.length := by simp only [trace,List.length_append,List.length_map]
      rw [traceLength]
      omega
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.Assembler
