module

public import Common.PSTR_SYM_CursorRound_052

/-! The SAME full cursor round in a fixed finite-label Bool machine.
Label choice and the whole transition table precede every input. This
does not parse the original outer input or implement its global loop. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorFinite

open Turing PSTRTMSeq005 PSTRSymbolicRelabel PSTRSymbolicCursorCode
open PSTRSymbolicLaneArchive PSTRSymbolicCursorRound PSTRTMIncrement009

def support : Finset Label := Finset.univ

noncomputable def labels : PointedMap Label (Fin (support.card + 1)) := finiteLabels support

noncomputable def cursorMachine : Machine support.card :=
  finiteMachine PSTRSymbolicCursorCode.machine support

theorem initial_label : labels (.mark 0) = 0 := by
  change labels (default : Label) = default
  exact labels.map_pt

theorem inverse_label (q : Label) : finiteDecode support (labels q) = q :=
  finite_inverse support q (Finset.mem_univ q)

theorem actual_step (state : TM0.Cfg Bool Label) :
    (TM0.step PSTRSymbolicCursorCode.machine state).map (relabelCfg labels) =
      TM0.step cursorMachine (relabelCfg labels state) :=
  relabel_step PSTRSymbolicCursorCode.machine (support : Set Label) labels (finiteDecode support)
    (by intro q _; exact inverse_label q) state (Finset.mem_univ state.q)

theorem actual_from_source (entry final : TM0.Cfg Bool Label)
    (trace : List (TM0.Cfg Bool Label))
    (first : trace.head? = some entry)
    (chain : trace.IsChain (fun before after => TM0.step PSTRSymbolicCursorCode.machine before = some after))
    (last : trace.getLast? = some final) (halt : TM0.step PSTRSymbolicCursorCode.machine final = none) :
    RunsFrom cursorMachine (relabelCfg labels entry) (trace.map (relabelCfg labels)) (relabelCfg labels final) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.head?_map,first,Option.map_some]
  · apply (List.isChain_map _).mpr
    apply chain.imp
    intro before after edge
    have step := actual_step before
    rw [edge] at step
    exact step.symm
  · simp only [List.getLast?_map,last,Option.map_some]
  · have step := actual_step final
    rw [halt] at step
    exact step.symm

theorem same_space (inputLength : Nat) (trace : List (TM0.Cfg Bool Label)) :
    visitedSpace cursorMachine inputLength (trace.map (relabelCfg labels)) =
      sourceVisitedSpace PSTRSymbolicCursorCode.machine inputLength trace :=
  relabel_visitedSpace PSTRSymbolicCursorCode.machine (support : Set Label) labels
    (finiteDecode support) (by intro q _; exact inverse_label q) inputLength trace
    (by intro state _; exact Finset.mem_univ state.q)

theorem actual_round (data : List Datum) (earlier later : List (Bool × Bool))
    (shape : allDatumPairs data = earlier ++ later) (base digits older suffix : List Bool)
    (rootFirst rootSecond rootThird near middle first far second tag : Bool)
    (headerShape : digits.reverse = rootFirst :: rootSecond :: rootThird :: older)
    (positive : true ∈ digits) :
    ∃ (trace : List (MachineState support.card)) (final : MachineState support.card),
      RunsFrom cursorMachine ⟨0,roundTape earlier base digits suffix near middle first far second tag⟩ trace final ∧
      final.q = labels (.halt (decide (valueDigits digits = 1))) ∧
      final.Tape = roundTape earlier base (PSTRTMThresholdCountdownCode164.predDigits digits)
        suffix near middle first far second tag ∧
      trace.length ≤ 4 * earlier.length + 10 * digits.length + 65 ∧
      ∀ inputLength clock, visitedSpace cursorMachine inputLength (trace.take clock) ≤
        inputLength + 8 * earlier.length + 20 * digits.length + 131 := by
  obtain ⟨sourceTrace,sourceFinal,firstHead,chain,lastHead,port,tape,halt,length⟩ :=
    PSTRSymbolicCursorRound.actual_round data earlier later shape base digits older suffix
      rootFirst rootSecond rootThird near middle first far second tag headerShape positive
  let trace := sourceTrace.map (relabelCfg labels)
  let final := relabelCfg labels sourceFinal
  have actual := actual_from_source
    ⟨.mark 0,roundTape earlier base digits suffix near middle first far second tag⟩
    sourceFinal sourceTrace firstHead chain lastHead halt
  have entry : relabelCfg labels
      (⟨.mark 0,roundTape earlier base digits suffix near middle first far second tag⟩ : TM0.Cfg Bool Label) =
      (⟨0,roundTape earlier base digits suffix near middle first far second tag⟩ : MachineState support.card) := by
    change (⟨labels (.mark 0),roundTape earlier base digits suffix near middle first far second tag⟩ : MachineState support.card) = _
    rw [initial_label]
  rw [entry] at actual
  refine ⟨trace,final,actual,?_,tape,?_,?_⟩
  · change labels sourceFinal.q = labels (.halt (decide (valueDigits digits = 1)))
    rw [port]
  · simpa only [trace,List.length_map] using length
  · intro inputLength clock
    have cells := PSTRTMTrace002.visitedSpace_le cursorMachine inputLength (trace.take clock)
    have takeLength : (trace.take clock).length ≤ sourceTrace.length := by
      simp only [List.length_take,trace,List.length_map]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCursorFinite
