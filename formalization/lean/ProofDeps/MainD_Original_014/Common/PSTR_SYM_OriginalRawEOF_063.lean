module

public import Common.PSTR_SYM_RawLoopRun_062

/-! SOURCEONLY. Original positive-N input to the actual restored EOF in
ONE source table, then a fixed finite Bool table. Its measured duration
is attached to this SAME witness. A uniform original-length polynomial
can subsequently bound the explicit data-dependent expression below. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop

open PaperProofs.Common Turing PSTRTMSeq005 PSTRSymbolicRelabel
open PSTRSymbolicRawBootstrap PSTRSymbolicPairedArchive PSTRSymbolicLaneScan PSTRSymbolicLaneArchive
open PSTRSymbolicCursorCode PSTRSymbolicCursorStages PSTRSymbolicCursorArchive PSTRTMIncrement009

theorem leaf_length_le_flatMap (data : List Datum) (value : Datum) (member : value ∈ data) :
    (encodeDatum value).length ≤ (data.flatMap encodeDatum).length := by
  obtain ⟨before,after,shape⟩ := List.mem_iff_append.mp member
  rw [shape]
  simp only [List.flatMap_append,List.flatMap_cons,List.length_append]
  omega

def rawEOFTime {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) : Nat :=
  1024 * ((CompactPrice.symbolicInput input available).length + 1)^2 +
    (originalRemaining input available).length *
      cycleBudget (allDatumPairs (rawInstance input ++ rawSet available)).length
        (afterTwo (rawInstance input ++ rawSet available).length).length
        ((rawInstance input ++ rawSet available).flatMap encodeDatum).length + 1

theorem original_source_eof {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool)
    (positive : 0 < I.stageCount) :
    ∃ (digits : List Bool) (trace : List (TM0.Cfg Bool LoopLabel)) (final : TM0.Cfg Bool LoopLabel),
      trace.head? = some (TM0.init (CompactPrice.symbolicInput input available)) ∧
      trace.IsChain (fun before after => TM0.step loopCode before = some after) ∧
      trace.getLast? = some final ∧ TM0.step loopCode final = none ∧
      final.Tape = archiveTape (rawInstance input ++ rawSet available) [] digits [] true ∧
      valueDigits digits = 0 ∧
      digits.length = (afterTwo (rawInstance input ++ rawSet available).length).length ∧
      trace.length ≤ rawEOFTime input available := by
  let data := rawInstance input ++ rawSet available
  let remaining := originalRemaining input available
  let pref := [Datum.natural I.stageCount,Datum.natural I.toolCount]
  let initialDigits := afterTwo data.length
  let bytes := (data.flatMap encodeDatum).length
  have fields : pref ++ remaining = data := by rfl
  have nonempty : remaining ≠ [] := by
    have room := original_positive_remaining input available positive
    intro empty
    change 3 ≤ remaining.length at room
    rw [empty] at room
    simp at room
  have prefixRoom : 3 ≤ (allDatumPairs pref).length := by
    have room := stage_tool_pairs_room I.stageCount I.toolCount
    change 4 ≤ (allDatumPairs pref).length at room
    omega
  have header := original_positive_header input available positive
  have sized : ∀ value ∈ remaining, (encodeDatum value).length ≤ bytes := by
    intro value member
    apply leaf_length_le_flatMap data value
    rw [← fields]
    exact List.mem_append.mpr (Or.inr member)
  obtain ⟨endDigits,loopTrace,loopFinal,loopHead,loopChain,loopLast,_,loopTape,loopNext,
    endValue,endWidth,loopTime⟩ :=
    actual_remaining pref remaining [] initialDigits bytes nonempty prefixRoom header.1
      (original_remaining_count input available) sized
  obtain ⟨bootTrace,bootFinal,bootRun,bootTape,_,bootTime,_⟩ := original_bootstrap input available
  have bootActual : RunsFrom bootstrapMachine ⟨0,Tape.mk₁ (CompactPrice.symbolicInput input available)⟩ bootTrace bootFinal :=
    ⟨bootRun.1,bootRun.2.1,bootRun.2.2.1,bootRun.2.2.2.1⟩
  have bootPart := called_endpoints loopCode bootstrapMachine LoopLabel.boot (fun _ => .datum 0)
    (by intro q bit; rfl) _ _ _ bootActual
  have physical : bootFinal.Tape = pendingTape pref [] initialDigits remaining := by
    rw [bootTape]
    simp only [bootstrapTape,pendingTape,pref,remaining,initialDigits,data,allDatumPairs_cells,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.reverse_append,List.append_assoc]
  have firstBridge : TM0.step loopCode (tagCfg LoopLabel.boot bootFinal) = some
      ⟨.datum 0,pendingTape pref [] initialDigits remaining⟩ := by
    simpa only [physical] using bootPart.2.2.2.1
  let throughLoop := bootTrace.map (tagCfg LoopLabel.boot) ++ loopTrace
  have throughChain : throughLoop.IsChain (fun before after => TM0.step loopCode before = some after) := by
    apply List.IsChain.append bootPart.2.1 loopChain
    intro before beforeLast after afterHead
    simp only [bootPart.2.2.1,Option.mem_some_iff] at beforeLast
    simp only [loopHead,Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact firstBridge
  have throughLast : throughLoop.getLast? = some loopFinal := by
    simp only [throughLoop,List.getLast?_append,loopLast,Option.some_or]
  let final : TM0.Cfg Bool LoopLabel := ⟨.done true,loopFinal.Tape⟩
  let trace := throughLoop ++ [final]
  have chain : trace.IsChain (fun before after => TM0.step loopCode before = some after) := by
    apply List.IsChain.append throughChain (.singleton _)
    intro before beforeLast after afterHead
    simp only [throughLast,Option.mem_some_iff] at beforeLast
    simp only [List.head?_cons,Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact loopNext
  have bootHead : (bootTrace.map (tagCfg LoopLabel.boot)).head? =
      some (TM0.init (CompactPrice.symbolicInput input available)) := bootPart.1
  rw [fields] at loopTape loopTime
  refine ⟨endDigits,trace,final,?_,chain,?_,loop_halt true _,loopTape,endValue,endWidth,?_⟩
  · simp only [trace,throughLoop,List.head?_append,bootHead,Option.some_or]
  · simp only [trace,List.getLast?_append,List.getLast?_singleton,Option.some_or]
  · change trace.length ≤ 1024 * ((CompactPrice.symbolicInput input available).length + 1)^2 +
      remaining.length * cycleBudget (allDatumPairs data).length initialDigits.length bytes + 1
    simp only [trace,throughLoop,List.length_append,List.length_map,List.length_cons,List.length_nil]
    omega

def loopSupport : Finset LoopLabel := Finset.univ

noncomputable def rawLoopMachine : Machine loopSupport.card := finiteMachine loopCode loopSupport

theorem loop_supports : TM0.Supports loopCode (loopSupport : Set LoopLabel) := by
  simpa only [loopSupport,Finset.coe_univ] using TM0.univ_supports loopCode

theorem original_raw_eof {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool)
    (positive : 0 < I.stageCount) :
    ∃ (digits : List Bool) (trace : List (MachineState loopSupport.card)) (final : MachineState loopSupport.card),
      Runs rawLoopMachine (CompactPrice.symbolicInput input available) trace final ∧
      final.Tape = archiveTape (rawInstance input ++ rawSet available) [] digits [] true ∧
      valueDigits digits = 0 ∧
      digits.length = (afterTwo (rawInstance input ++ rawSet available).length).length ∧
      trace.length ≤ rawEOFTime input available ∧
      ∀ clock, visitedSpace rawLoopMachine (CompactPrice.symbolicInput input available).length (trace.take clock) ≤
        (CompactPrice.symbolicInput input available).length + 2 * rawEOFTime input available + 1 := by
  obtain ⟨digits,oldTrace,oldFinal,firstHead,chain,lastHead,halt,tape,value,width,time⟩ :=
    original_source_eof input available positive
  let trace := oldTrace.map (relabelCfg (finiteLabels loopSupport))
  let final := relabelCfg (finiteLabels loopSupport) oldFinal
  have actual := finite_runs loopCode loopSupport loop_supports _ oldTrace oldFinal firstHead chain lastHead halt
  have mappedLength : trace.length = oldTrace.length := List.length_map _
  refine ⟨digits,trace,final,actual,tape,value,width,?_,?_⟩
  · rw [mappedLength]
    exact time
  · intro clock
    have cells := PSTRTMTrace002.visitedSpace_le rawLoopMachine
      (CompactPrice.symbolicInput input available).length (trace.take clock)
    have taken : (trace.take clock).length ≤ oldTrace.length := by
      simp only [List.length_take,mappedLength]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop
