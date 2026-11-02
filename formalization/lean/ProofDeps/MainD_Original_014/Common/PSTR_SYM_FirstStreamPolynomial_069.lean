module

public import Common.PSTR_SYM_FirstStreamRun_068

/-! Finite Bool native execution of the SAME suffix-preserving first
stream. The constants precede all fields. The untouched unread stream
contributes to the genuine original-input space accounting. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop

open Turing PSTRTMSeq005 PSTRSymbolicRelabel PSTRTMIncrement009
open PSTRSymbolicRawBootstrap PSTRSymbolicCounter PSTRSymbolicLaneArchive PSTRSymbolicCursorArchive

theorem stream_time_polynomial (first second : Nat) (remaining : List Datum) (unread : List Bool) :
    streamTime first second remaining unread ≤
      4096 * ((encode (streamData first second remaining) ++ unread).length + 1)^3 := by
  let data := streamData first second remaining
  let size := (encode data ++ unread).length
  let payload := (data.flatMap encodeDatum).length
  let pairs := (allDatumPairs data).length
  let width := (afterTwo data.length).length
  have layout : size = 2 * natBits data.length + 2 + payload + unread.length := by
    simp only [size,encode,List.length_append,PSTRTMLength004.encodeNat_length,List.length_singleton]
    omega
  have payloadRoom : payload ≤ size := by omega
  have pairSizes : 2 * pairs = payload := pairs_bytes data
  have pairsRoom : pairs ≤ size := by omega
  have countRoom : data.length ≤ size := (count_bytes data).trans payloadRoom
  have fields : data = .natural first :: .natural second :: remaining := rfl
  have length := congrArg List.length fields
  simp only [List.length_cons] at length
  have remainingRoom : remaining.length ≤ size := by omega
  have enough : 2 ≤ data.length := by omega
  have widthEqual : width = natBits data.length := by
    change (afterTwo data.length).length = _
    rw [(two_count_rounds data.length enough).2.2.2,PSTRSymbolicLocator.rawPayload_length]
  have widthRoom : width ≤ size := by rw [widthEqual]; omega
  have square := Nat.pow_le_pow_left (Nat.add_le_add_right payloadRoom 1) 2
  have bodyRoom : cycleBudget pairs width payload ≤ 512 * (size + 1)^2 := by
    unfold cycleBudget
    nlinarith [Nat.zero_le (size^2)]
  have totalRoom := Nat.mul_le_mul remainingRoom bodyRoom
  change 1024 * (size + 1)^2 + remaining.length * cycleBudget pairs width payload + 1 ≤
    4096 * (size + 1)^3
  nlinarith [Nat.zero_le (size^2),Nat.zero_le (size^3)]

theorem actual_first_stream (first second : Nat) (remaining : List Datum) (unread : List Bool)
    (room : 2 ≤ remaining.length) :
    ∃ (digits : List Bool) (trace : List (MachineState loopSupport.card)) (final : MachineState loopSupport.card),
      Runs rawLoopMachine (encode (streamData first second remaining) ++ unread) trace final ∧
      final.Tape = archiveTape (streamData first second remaining) [] digits unread true ∧
      final.Tape.head = true ∧ final.Tape.right = ListBlank.mk unread ∧
      valueDigits digits = 0 ∧ 3 ≤ digits.length ∧
      trace.length ≤ 4096 * ((encode (streamData first second remaining) ++ unread).length + 1)^3 ∧
      ∀ clock, visitedSpace rawLoopMachine (encode (streamData first second remaining) ++ unread).length
        (trace.take clock) ≤ 16384 * ((encode (streamData first second remaining) ++ unread).length + 1)^3 := by
  obtain ⟨digits,oldTrace,oldFinal,firstHead,chain,lastHead,halt,tape,value,width,time⟩ :=
    actual_first_stream_source first second remaining unread room
  let bits := encode (streamData first second remaining) ++ unread
  let trace := oldTrace.map (relabelCfg (finiteLabels loopSupport))
  let final := relabelCfg (finiteLabels loopSupport) oldFinal
  have finalTape : final.Tape = archiveTape (streamData first second remaining) [] digits unread true := tape
  have actual := finite_runs loopCode loopSupport loop_supports bits oldTrace oldFinal firstHead chain lastHead halt
  have mappedLength : trace.length = oldTrace.length := List.length_map _
  have polynomial := stream_time_polynomial first second remaining unread
  have header := (stream_header first second remaining room).1
  have sizeRoom : bits.length + 1 ≤ (bits.length + 1)^3 := by
    nlinarith [Nat.zero_le (bits.length^2),Nat.zero_le (bits.length^3)]
  refine ⟨digits,trace,final,actual,finalTape,?_,?_,value,?_,?_,?_⟩
  · rw [finalTape]
    rfl
  · rw [finalTape]
    rfl
  · rw [width]
    exact header
  · rw [mappedLength]
    exact time.trans polynomial
  · intro clock
    have cells := PSTRTMTrace002.visitedSpace_le rawLoopMachine bits.length (trace.take clock)
    have takeLength : (trace.take clock).length ≤ oldTrace.length := by
      simp only [List.length_take,mappedLength]
      omega
    change visitedSpace rawLoopMachine bits.length (trace.take clock) ≤ 16384 * (bits.length + 1)^3
    change streamTime first second remaining unread ≤ 4096 * (bits.length + 1)^3 at polynomial
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop
