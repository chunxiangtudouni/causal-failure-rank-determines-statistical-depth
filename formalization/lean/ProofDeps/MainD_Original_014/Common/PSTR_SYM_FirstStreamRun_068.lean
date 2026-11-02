module

public import Common.PSTR_SYM_RawLoopSuffix_067

/-! The same fixed raw parser reads ONE genuine counted stream followed
by arbitrary unread bits. All data/header sizes below measure the actual
run; they are not code parameters. No blank-right claim is made. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop

open PaperProofs.Common Turing PSTRTMSeq005 PSTRSymbolicRelabel
open PSTRSymbolicRawBootstrap PSTRSymbolicPairedArchive PSTRSymbolicLaneScan PSTRSymbolicLaneArchive
open PSTRSymbolicCursorCode PSTRSymbolicCursorStages PSTRSymbolicCursorArchive PSTRTMIncrement009
open PSTRSymbolicCounter

def streamData (first second : Nat) (remaining : List Datum) : List Datum :=
  .natural first :: .natural second :: remaining

def streamTime (first second : Nat) (remaining : List Datum) (unread : List Bool) : Nat :=
  let data := streamData first second remaining
  1024 * ((encode data ++ unread).length + 1)^2 + remaining.length *
    cycleBudget (allDatumPairs data).length (afterTwo data.length).length (data.flatMap encodeDatum).length + 1

theorem stream_header (first second : Nat) (remaining : List Datum) (room : 2 ≤ remaining.length) :
    3 ≤ (afterTwo (streamData first second remaining).length).length ∧
      valueDigits (afterTwo (streamData first second remaining).length) = remaining.length := by
  let count := (streamData first second remaining).length
  have countLength : count = remaining.length + 2 := by simp only [count,streamData,List.length_cons]
  have countRoom : 4 ≤ count := by omega
  have rounds := two_count_rounds count (by omega)
  have logRoom : natBits 4 ≤ natBits count := by
    simp only [natBits,Nat.log2_eq_log_two]
    exact Nat.add_le_add_right (Nat.log_mono_right countRoom) 1
  have four : natBits 4 = 3 := by decide
  rw [four] at logRoom
  refine ⟨?_,?_⟩
  · change 3 ≤ (afterTwo count).length
    rw [rounds.2.2.2,PSTRSymbolicLocator.rawPayload_length]
    exact logRoom
  · change valueDigits (afterTwo count) = remaining.length
    omega

theorem actual_first_stream_source (first second : Nat) (remaining : List Datum) (unread : List Bool)
    (room : 2 ≤ remaining.length) :
    ∃ (digits : List Bool) (trace : List (TM0.Cfg Bool LoopLabel)) (final : TM0.Cfg Bool LoopLabel),
      trace.head? = some (TM0.init (encode (streamData first second remaining) ++ unread)) ∧
      trace.IsChain (fun before after => TM0.step loopCode before = some after) ∧
      trace.getLast? = some final ∧ TM0.step loopCode final = none ∧
      final.Tape = archiveTape (streamData first second remaining) [] digits unread true ∧
      valueDigits digits = 0 ∧
      digits.length = (afterTwo (streamData first second remaining).length).length ∧
      trace.length ≤ streamTime first second remaining unread := by
  let data := streamData first second remaining
  let count := data.length
  let pref := [Datum.natural first,Datum.natural second]
  let initialDigits := afterTwo count
  let bytes := (data.flatMap encodeDatum).length
  let suffix := remaining.flatMap encodeDatum ++ true :: unread
  have fields : pref ++ remaining = data := rfl
  have countRoom : 2 ≤ count := by simp only [count,data,streamData,List.length_cons]; omega
  have header := stream_header first second remaining room
  have nonempty : remaining ≠ [] := by intro empty; rw [empty,List.length_nil] at room; omega
  have prefixRoom : 3 ≤ (allDatumPairs pref).length := by
    have enough := stage_tool_pairs_room first second
    change 4 ≤ (allDatumPairs pref).length at enough
    omega
  have sized : ∀ value ∈ remaining, (encodeDatum value).length ≤ bytes := by
    intro value member
    apply leaf_length_le_flatMap data value
    rw [← fields]
    exact List.mem_append.mpr (Or.inr member)
  obtain ⟨endDigits,loopTrace,loopFinal,loopHead,loopChain,loopLast,_,loopTape,loopNext,
    endValue,endWidth,loopTime⟩ := actual_remaining_suffix pref remaining [] initialDigits unread bytes
      nonempty prefixRoom header.1 header.2 sized
  obtain ⟨bootTrace,bootFinal,bootRun,bootTape,_,bootTime,_⟩ :=
    bootstrap_polynomial count first second suffix countRoom
  have bits : bootstrapInput count first second suffix = encode data ++ unread := by
    simp only [bootstrapInput,suffix,encode,count,data,streamData,List.flatMap_cons,
      List.append_assoc,List.singleton_append]
  rw [bits] at bootRun bootTime
  have bootActual : RunsFrom bootstrapMachine ⟨0,Tape.mk₁ (encode data ++ unread)⟩ bootTrace bootFinal :=
    ⟨bootRun.1,bootRun.2.1,bootRun.2.2.1,bootRun.2.2.2.1⟩
  have bootPart := called_endpoints loopCode bootstrapMachine LoopLabel.boot (fun _ => .datum 0)
    (by intro q bit; rfl) _ _ _ bootActual
  have physical : bootFinal.Tape = pendingSuffix pref [] initialDigits remaining unread := by
    rw [bootTape]
    simp only [bootstrapTape,pendingSuffix,pref,initialDigits,suffix,allDatumPairs_cells,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.reverse_append,List.append_assoc]
  have firstBridge : TM0.step loopCode (tagCfg LoopLabel.boot bootFinal) = some
      ⟨.datum 0,pendingSuffix pref [] initialDigits remaining unread⟩ := by
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
  rw [fields] at loopTape loopTime
  have bootHead : (bootTrace.map (tagCfg LoopLabel.boot)).head? =
      some (TM0.init (encode data ++ unread)) := bootPart.1
  have bootClock := bootTime
  simp only [List.length_append] at bootClock
  refine ⟨endDigits,trace,final,?_,chain,?_,loop_halt true _,loopTape,endValue,endWidth,?_⟩
  · simp only [trace,throughLoop,List.head?_append,bootHead,Option.some_or]
    rfl
  · simp only [trace,List.getLast?_append,List.getLast?_singleton,Option.some_or]
  · change trace.length ≤ 1024 * ((encode data ++ unread).length + 1)^2 +
      remaining.length * cycleBudget (allDatumPairs data).length initialDigits.length bytes + 1
    simp only [trace,throughLoop,List.length_append,List.length_map,List.length_cons,List.length_nil]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop
