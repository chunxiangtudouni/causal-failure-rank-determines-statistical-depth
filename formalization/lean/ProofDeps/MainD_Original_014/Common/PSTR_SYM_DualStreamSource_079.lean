module

public import Common.PSTR_SYM_PositivePacketRun_078

/-! The SAME fixed075 whole parser really branches on the second
stream's count. Both branches terminate at a genuine global HALT.
The two physical archives remain explicit; this is not a planner action
computation or an Expr serializer. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream

open PaperProofs.Common Turing PSTRTMSeq005 PSTRTMIncrement009
open PSTRSymbolicRawLoop PSTRSymbolicRawBootstrap PSTRSymbolicRetainedBootstrap
open PSTRSymbolicCursorArchive

def recordEndTape (data : List Datum) (firstDigits : List Bool) (records : List Nat)
    (secondDigits : List Bool) : Tape Bool :=
  let archive := PSTRSymbolicRawStack.archiveLeft data firstDigits
  if records = [] then Tape.mk₂ (false :: false :: true :: false :: archive) [true]
  else archiveTape (records.map Datum.natural) archive secondDigits [] true

theorem positive_gate_start (data : List Datum) (digits : List Bool) (records : List Nat)
    (large : 4 ≤ records.length) :
    TM0.step dualCode (gateEnd data digits records) = some
      ⟨.boot 0,Tape.mk₂ (false :: PSTRSymbolicRawStack.archiveLeft data digits)
        (encode (records.map Datum.natural))⟩ := by
  have nonempty : records.map Datum.natural ≠ [] := by
    intro empty
    have length := congrArg List.length empty
    simp only [List.length_map,List.length_nil] at length
    omega
  have control := PSTRTML01RecordGate251.final_control
    (false :: PSTRSymbolicRawStack.archiveLeft data digits) (records.map Datum.natural) []
  simp only [nonempty,ite_false] at control
  have physical : (gateEnd data digits records).Tape =
      Tape.mk₂ (false :: PSTRSymbolicRawStack.archiveLeft data digits)
        (encode (records.map Datum.natural)) := by
    change (PSTRTML01RecordGate251.final _ _ _).Tape = _
    simpa only [nonempty,ite_false,List.append_nil] using
      PSTRTML01RecordGate251.final_tape
        (false :: PSTRSymbolicRawStack.archiveLeft data digits) (records.map Datum.natural) []
  simpa only [control,gate_positive,physical] using gate_end_next data digits records

theorem zero_gate_start (data : List Datum) (digits : List Bool) :
    TM0.step dualCode (gateEnd data digits []) = some
      ⟨.halt true,recordEndTape data digits [] []⟩ := by
  exact gate_end_next data digits []

theorem actual_original_dual_source {I : Instance} (input : StatisticalInput I) (contract : Contract I)
    (available : Finset I.Tool) (budget : Rat) (history : List (VisibleEvent I)) (records : List Nat)
    (domain : records = [] ∨ 4 ≤ records.length) :
    ∃ (firstDigits secondDigits : List Bool) (trace : List (TM0.Cfg Bool Label)) (final : TM0.Cfg Bool Label),
      trace.head? = some (TM0.init (CompactPrice.plannerInput input contract available budget history records)) ∧
      trace.IsChain (fun before after => TM0.step dualCode before = some after) ∧
      trace.getLast? = some final ∧ TM0.step dualCode final = none ∧
      final.Tape = recordEndTape (PSTRTablePlannerStreams.firstData input contract available budget history)
        firstDigits records secondDigits ∧
      valueDigits firstDigits = 0 ∧ 3 ≤ firstDigits.length ∧ valueDigits secondDigits = 0 ∧
      trace.length ≤ 16384 * ((CompactPrice.plannerInput input contract available budget history records).length + 1)^3 := by
  let data := PSTRTablePlannerStreams.firstData input contract available budget history
  let bits := CompactPrice.plannerInput input contract available budget history records
  obtain ⟨digits,firstTrace,firstHead,firstChain,firstLast,value,width,firstTime⟩ :=
    actual_original_gate_entry input contract available budget history records domain
  let firstPart : RunPart dualCode (TM0.init bits) (gateEnd data digits records) :=
    ⟨firstTrace,firstHead,firstChain,firstLast⟩
  have sizePositive : 1 ≤ (bits.length + 1)^3 := by
    nlinarith [Nat.zero_le (bits.length^2),Nat.zero_le (bits.length^3)]
  rcases domain with empty | large
  · subst records
    let final : TM0.Cfg Bool Label := ⟨.halt true,recordEndTape data digits [] []⟩
    let endPart : RunPart dualCode final final := ⟨[final],rfl,.singleton _,rfl⟩
    let all := firstPart.append endPart (zero_gate_start data digits)
    refine ⟨digits,[],all.trace,final,all.head,all.chain,all.last,terminal true _,rfl,value,width,rfl,?_⟩
    have length : all.trace.length = firstTrace.length + 1 := by
      simp only [all,RunPart.append_length]
      rfl
    rw [length]
    change firstTrace.length + 1 ≤ 16384 * (bits.length + 1)^3
    change firstTrace.length ≤ 4096 * (bits.length + 1)^3 + 7 at firstTime
    omega
  · obtain ⟨first,second,later,fields,laterRoom⟩ := record_values_decompose records large
    let recordData := records.map Datum.natural
    let archive := PSTRSymbolicRawStack.archiveLeft data digits
    have recordShape : recordData = streamData first second (later.map Datum.natural) := by
      change records.map Datum.natural = _
      rw [fields]
      rfl
    have room : 2 ≤ (later.map Datum.natural).length := by simpa only [List.length_map] using laterRoom
    obtain ⟨endDigits,secondTrace,final,secondHead,secondChain,secondLast,_port,halt,tape,endValue,_endWidth,secondTime⟩ :=
      actual_positive_packet archive first second (later.map Datum.natural) room
    rw [← recordShape] at secondHead tape
    let secondPart : RunPart dualCode
        ⟨.boot 0,Tape.mk₂ (false :: archive) (encode recordData)⟩ final :=
      ⟨secondTrace,secondHead,secondChain,secondLast⟩
    let all := firstPart.append secondPart (positive_gate_start data digits records large)
    have nonempty : records ≠ [] := by intro empty; rw [empty,List.length_nil] at large; omega
    have finalTape : final.Tape = recordEndTape data digits records endDigits := by
      simpa only [recordEndTape,nonempty,ite_false] using tape
    have encodedRoom : (encode (streamData first second (later.map Datum.natural)) ++ []).length ≤ bits.length := by
      simp only [List.append_nil]
      rw [← recordShape]
      have original := PSTRTablePlannerStreams.original_two_streams input contract available budget history records
      change bits = encode data ++ encode recordData at original
      rw [original,List.length_append]
      omega
    have secondPolynomial := (stream_time_polynomial first second (later.map Datum.natural) []).trans
      (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left (Nat.add_le_add_right encodedRoom 1) 3))
    have secondClock : secondTrace.length ≤ 4096 * (bits.length + 1)^3 + 1 :=
      secondTime.trans (Nat.add_le_add_right secondPolynomial 1)
    have length : all.trace.length = firstTrace.length + secondTrace.length := by
      simp only [all,RunPart.append_length]
      rfl
    refine ⟨digits,endDigits,all.trace,final,all.head,all.chain,all.last,halt,finalTape,value,width,endValue,?_⟩
    rw [length]
    change firstTrace.length + secondTrace.length ≤ 16384 * (bits.length + 1)^3
    change firstTrace.length ≤ 4096 * (bits.length + 1)^3 + 7 at firstTime
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream
