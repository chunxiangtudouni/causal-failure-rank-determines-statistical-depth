module

public import RootB234_PrepEntry_RawData_019

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.Raw

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMWordPreparationFront214 PSTRTMSeq005 PSTRTMIncrement009
open PSTRSymbolicRawBootstrap PSTRSymbolicCounter PSTRSymbolicRawLoop PSTRSymbolicLaneArchive
open PSTRSymbolicRelabel PSTRSymbolicPairedArchive PSTRSymbolicLaneScan PSTRSymbolicCursorArchive
open PA17TMRatArithmeticParse002 PSTRSymbolicCursorStages PSTRSymbolicCursorCode

variable {I : Instance}

def rawEOFTime {I : Instance} (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : Nat :=
  1024 * ((preparationInput input contract budget).length + 1)^2 +
    (RootB234.PrepEntry.Raw.remaining input contract budget).length *
      cycleBudget (allDatumPairs (preparationData input contract budget)).length
        (afterTwo (preparationData input contract budget).length).length
        ((preparationData input contract budget).flatMap encodeDatum).length + 1

theorem preparation_source_eof {I : Instance} (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (digits : List Bool) (trace : List (TM0.Cfg Bool LoopLabel)) (final : TM0.Cfg Bool LoopLabel),
      trace.head? = some (TM0.init (preparationInput input contract budget)) ∧
      trace.IsChain (fun before after => TM0.step loopCode before = some after) ∧
      trace.getLast? = some final ∧ TM0.step loopCode final = none ∧
      final.Tape = archiveTape (preparationData input contract budget) [] digits [] true ∧
      valueDigits digits = 0 ∧
      digits.length = (afterTwo (preparationData input contract budget).length).length ∧
      trace.length ≤ rawEOFTime input contract budget := by
  let data := preparationData input contract budget
  let remaining := RootB234.PrepEntry.Raw.remaining input contract budget
  let pref := [Datum.natural I.stageCount,Datum.natural I.toolCount]
  let initialDigits := afterTwo data.length
  let bytes := (data.flatMap encodeDatum).length
  have fields : pref ++ remaining = data := by rfl
  have nonempty : remaining ≠ [] := by
    have room := remaining_room input contract budget
    intro empty
    change 6 ≤ remaining.length at room
    rw [empty] at room
    simp at room
  have prefixRoom : 3 ≤ (allDatumPairs pref).length := by
    have room := stage_tool_pairs_room I.stageCount I.toolCount
    change 4 ≤ (allDatumPairs pref).length at room
    omega
  have header := header_room input contract budget
  have sized : ∀ value ∈ remaining, (encodeDatum value).length ≤ bytes := by
    intro value member
    apply leaf_length_le_flatMap data value
    rw [← fields]
    exact List.mem_append.mpr (Or.inr member)
  obtain ⟨endDigits,loopTrace,loopFinal,loopHead,loopChain,loopLast,_,loopTape,loopNext,
    endValue,endWidth,loopTime⟩ :=
    actual_remaining pref remaining [] initialDigits bytes nonempty prefixRoom header
      (remaining_count input contract budget) sized
  obtain ⟨bootTrace,bootFinal,bootRun,bootTape,_,bootTime,_⟩ := preparation_bootstrap input contract budget
  have bootActual : RunsFrom bootstrapMachine ⟨0,Tape.mk₁ (preparationInput input contract budget)⟩ bootTrace bootFinal :=
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
      some (TM0.init (preparationInput input contract budget)) := bootPart.1
  rw [fields] at loopTape loopTime
  refine ⟨endDigits,trace,final,?_,chain,?_,loop_halt true _,loopTape,endValue,endWidth,?_⟩
  · simp only [trace,throughLoop,List.head?_append,bootHead,Option.some_or]
  · simp only [trace,List.getLast?_append,List.getLast?_singleton,Option.some_or]
  · change trace.length ≤ 1024 * ((preparationInput input contract budget).length + 1)^2 +
      remaining.length * cycleBudget (allDatumPairs data).length initialDigits.length bytes + 1
    simp only [trace,throughLoop,List.length_append,List.length_map,List.length_cons,List.length_nil]
    omega

theorem raw_eof_time_polynomial {I : Instance} (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    rawEOFTime input contract budget ≤ 4096 * ((preparationInput input contract budget).length + 1)^3 := by
  let data := preparationData input contract budget
  let remaining := RootB234.PrepEntry.Raw.remaining input contract budget
  let size := (preparationInput input contract budget).length
  let payload := (data.flatMap encodeDatum).length
  let pairs := (allDatumPairs data).length
  let width := (afterTwo data.length).length
  have layout : size = 2 * natBits data.length + 2 + payload := by
    change (encode data).length = _
    simp only [encode,List.length_append,PSTRTMLength004.encodeNat_length,List.length_singleton]
    omega
  have payloadRoom : payload ≤ size := by omega
  have pairSizes : 2 * pairs = payload := pairs_bytes data
  have pairsRoom : pairs ≤ size := by omega
  have countRoom : data.length ≤ size := (count_bytes data).trans payloadRoom
  have fields : data = .natural I.stageCount :: .natural I.toolCount :: remaining := rfl
  have length := congrArg List.length fields
  simp only [List.length_cons] at length
  have remainingRoom : remaining.length ≤ size := by omega
  have widthEqual : width = natBits data.length := by
    change (afterTwo data.length).length = _
    rw [(two_count_rounds data.length (by have room:=count_room input contract budget; omega)).2.2.2,
      PSTRSymbolicLocator.rawPayload_length]
  have widthRoom : width ≤ size := by rw [widthEqual]; omega
  have square := Nat.pow_le_pow_left (Nat.add_le_add_right payloadRoom 1) 2
  have bodyRoom : cycleBudget pairs width payload ≤ 512 * (size + 1)^2 := by
    unfold cycleBudget
    nlinarith [Nat.zero_le (size^2)]
  have totalRoom := Nat.mul_le_mul remainingRoom bodyRoom
  change 1024 * (size + 1)^2 + remaining.length * cycleBudget pairs width payload + 1 ≤
    4096 * (size + 1)^3
  nlinarith [Nat.zero_le (size^2),Nat.zero_le (size^3)]

theorem preparation_raw_eof {I : Instance} (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (digits : List Bool) (trace : List (MachineState loopSupport.card)) (final : MachineState loopSupport.card),
      Runs rawLoopMachine (preparationInput input contract budget) trace final ∧
      final.Tape = archiveTape (preparationData input contract budget) [] digits [] true ∧
      valueDigits digits = 0 ∧
      digits.length = (afterTwo (preparationData input contract budget).length).length ∧
      trace.length ≤ rawEOFTime input contract budget ∧
      ∀ clock, visitedSpace rawLoopMachine (preparationInput input contract budget).length (trace.take clock) ≤
        (preparationInput input contract budget).length + 2 * rawEOFTime input contract budget + 1 := by
  obtain ⟨digits,oldTrace,oldFinal,firstHead,chain,lastHead,halt,tape,value,width,time⟩ :=
    preparation_source_eof input contract budget
  let trace := oldTrace.map (relabelCfg (finiteLabels loopSupport))
  let final := relabelCfg (finiteLabels loopSupport) oldFinal
  have actual := finite_runs loopCode loopSupport loop_supports _ oldTrace oldFinal firstHead chain lastHead halt
  have mappedLength : trace.length = oldTrace.length := List.length_map _
  refine ⟨digits,trace,final,actual,tape,value,width,?_,?_⟩
  · rw [mappedLength]
    exact time
  · intro clock
    have cells := PSTRTMTrace002.visitedSpace_le rawLoopMachine
      (preparationInput input contract budget).length (trace.take clock)
    have taken : (trace.take clock).length ≤ oldTrace.length := by
      simp only [List.length_take,mappedLength]
      omega
    omega


theorem preparation_raw_polynomial (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (digits : List Bool) (trace : List (MachineState loopSupport.card)) (final : MachineState loopSupport.card),
      Runs rawLoopMachine (preparationInput input contract budget) trace final ∧
      final.Tape=archiveTape (preparationData input contract budget) [] digits [] true ∧
      valueDigits digits=0 ∧ 3≤digits.length ∧
      trace.length≤4096*((preparationInput input contract budget).length+1)^3 ∧
      ∀ clock,visitedSpace rawLoopMachine (preparationInput input contract budget).length (trace.take clock)≤
        16384*((preparationInput input contract budget).length+1)^3 := by
  obtain ⟨digits,trace,final,actual,tape,value,width,time,space⟩:=preparation_raw_eof input contract budget
  have timeCap:=raw_eof_time_polynomial input contract budget
  refine ⟨digits,trace,final,actual,tape,value,?_,time.trans timeCap,?_⟩
  · rw [width]
    exact header_room input contract budget
  · intro clock
    have old:=space clock
    have base : 1≤(preparationInput input contract budget).length+1 := by omega
    have linear : (preparationInput input contract budget).length+1≤((preparationInput input contract budget).length+1)^3 := by
      simpa only [pow_one] using Nat.pow_le_pow_right base (by decide : (1:Nat)≤3)
    nlinarith only [old,timeCap,linear]

end RootB234.PrepEntry.Raw
