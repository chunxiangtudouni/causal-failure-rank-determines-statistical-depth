module

public import Common.PSTR_SYM_RecordPacket_077

/-! SAME075code, real retained native bootstrap followed by the actual
remaining body and its charged return to global HALT. Entry is the actual
positive gate's next control/Tape, not a free raw reset. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream

open Turing PSTRTMSeq005 PSTRTMIncrement009 PSTRSymbolicCursorCode
open PSTRSymbolicRawBootstrap PSTRSymbolicRetainedBootstrap PSTRSymbolicRawLoop
open PSTRSymbolicNativeRemaining PSTRSymbolicLaneArchive PSTRSymbolicCursorArchive

theorem actual_positive_packet (archive : List Bool) (first second : Nat) (remaining : List Datum)
    (room : 2 ≤ remaining.length) :
    ∃ (digits : List Bool) (trace : List (TM0.Cfg Bool Label)) (final : TM0.Cfg Bool Label),
      trace.head? = some ⟨.boot 0,Tape.mk₂ (false :: archive) (encode (streamData first second remaining))⟩ ∧
      trace.IsChain (fun before after => TM0.step dualCode before = some after) ∧
      trace.getLast? = some final ∧ final.q = .halt false ∧ TM0.step dualCode final = none ∧
      final.Tape = archiveTape (streamData first second remaining) archive digits [] true ∧
      valueDigits digits = 0 ∧ digits.length = (afterTwo (streamData first second remaining).length).length ∧
      trace.length ≤ streamTime first second remaining [] + 1 := by
  let data := streamData first second remaining
  let count := data.length
  let seed := [Datum.natural first,Datum.natural second]
  let initialDigits := afterTwo count
  let bytes := (data.flatMap encodeDatum).length
  let suffix := remaining.flatMap encodeDatum ++ [true]
  have fields : seed ++ remaining = data := rfl
  have enough : 2 ≤ count := by simp only [count,data,streamData,List.length_cons]; omega
  obtain ⟨bootTrace,bootFinal,bootRun,_bootPort,bootTape,bootTime,_bootSpace⟩ :=
    actual_native_bootstrap_from_guard count first second archive suffix enough
  have bits : bootstrapInput count first second suffix = encode data := by
    simpa only [List.append_nil] using bootstrap_stream_bits first second remaining []
  rw [bits] at bootRun
  have pending : bootFinal.Tape = pendingSuffix seed archive initialDigits remaining [] := by
    rw [bootTape]
    exact bootstrap_is_pending archive count first second remaining []
  have header := stream_header first second remaining room
  have archiveRoom : 3 ≤ (allDatumPairs seed).length := by
    have seedRoom := stage_tool_pairs_room first second
    change 4 ≤ (allDatumPairs seed).length at seedRoom
    omega
  have nonempty : remaining ≠ [] := by intro empty; rw [empty,List.length_nil] at room; omega
  have sized : ∀ value ∈ remaining, (encodeDatum value).length ≤ bytes := by
    intro value member
    apply leaf_length_le_flatMap data value
    rw [← fields]
    exact List.mem_append.mpr (Or.inr member)
  obtain ⟨digits,remainingTrace,remainingFinal,remainingRun,_remainingPort,remainingTape,
    value,width,remainingTime,_remainingSpace⟩ := actual_native_remaining seed remaining archive initialDigits [] bytes
      nonempty archiveRoom header.1 header.2 sized
  let bootPart := nativePart dualCode bootstrapMachine Label.boot (fun _ => .remaining entryLabel)
    (by intro q bit; rfl) _ _ _ bootRun
  let remainingPart := nativePart dualCode rawLoopMachine Label.remaining (fun _ => .halt false)
    (by intro q bit; rfl) _ _ _ remainingRun
  have bridgeBoot : TM0.step dualCode (tagCfg Label.boot bootFinal) =
      some (tagCfg Label.remaining (⟨entryLabel,pendingSuffix seed archive initialDigits remaining []⟩ : MachineState loopSupport.card)) := by
    simpa only [tagCfg,pending] using boot_return bootFinal bootRun.2.2.2
  let final : TM0.Cfg Bool Label := ⟨.halt false,remainingFinal.Tape⟩
  let terminalPart : RunPart dualCode final final := ⟨[final],rfl,.singleton _,rfl⟩
  have bridgeRemaining : TM0.step dualCode (tagCfg Label.remaining remainingFinal) = some final :=
    remaining_return remainingFinal remainingRun.2.2.2
  let all := (bootPart.append remainingPart bridgeBoot).append terminalPart bridgeRemaining
  rw [fields] at remainingTape remainingTime
  have bootBound := bootTime.trans (bootstrap_cost_encoded first second remaining)
  change bootTrace.length ≤ 1024 * ((encode data).length + 1)^2 at bootBound
  have bootLength : bootPart.trace.length = bootTrace.length := List.length_map _
  have remainingLength : remainingPart.trace.length = remainingTrace.length := List.length_map _
  have terminalLength : terminalPart.trace.length = 1 := rfl
  refine ⟨digits,all.trace,final,?_,all.chain,all.last,rfl,terminal false _,remainingTape,value,width,?_⟩
  · exact all.head
  · change all.trace.length ≤ 1024 * ((encode data ++ []).length + 1)^2 +
      remaining.length * cycleBudget (allDatumPairs data).length initialDigits.length bytes + 1 + 1
    simp only [all,RunPart.append_length,bootLength,remainingLength,terminalLength,List.append_nil]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream
