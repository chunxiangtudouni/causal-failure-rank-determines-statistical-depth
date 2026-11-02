module

public import Common.PSTR_SYM_DualStreamCode_075
public import Common.PSTR_SYM_RawStackProducer_065

/-! ORIGINAL planner input -> SAME whole first parser/real guard/record
gate. The returned gate port is ACTIVE in this containing code; its
old standalone HALT has a real next edge, exposed below and not erased.
The positive second bootstrap/remaining run is not claimed by this prefix. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream

open PaperProofs.Common Turing PSTRTMSeq005 PSTRSymbolicCursorCode PSTRSymbolicRawBootstrap
open PSTRSymbolicRawLoop PSTRSymbolicRetainedBootstrap PSTRSymbolicPlannerParser PSTRTMIncrement009

def gateEnd (data : List Datum) (digits : List Bool) (records : List Nat) : TM0.Cfg Bool Label :=
  tagCfg Label.gate (PSTRTML01RecordGate251.final
    (false :: PSTRSymbolicRawStack.archiveLeft data digits) (records.map Datum.natural) [])

theorem actual_original_gate_entry {I : Instance} (input : StatisticalInput I) (contract : Contract I)
    (available : Finset I.Tool) (budget : Rat) (history : List (VisibleEvent I)) (records : List Nat)
    (domain : records = [] ∨ 4 ≤ records.length) :
    ∃ (digits : List Bool) (trace : List (TM0.Cfg Bool Label)),
      trace.head? = some (TM0.init (CompactPrice.plannerInput input contract available budget history records)) ∧
      trace.IsChain (fun before after => TM0.step dualCode before = some after) ∧
      trace.getLast? = some (gateEnd (PSTRTablePlannerStreams.firstData input contract available budget history) digits records) ∧
      valueDigits digits = 0 ∧ 3 ≤ digits.length ∧
      trace.length ≤ 4096 * ((CompactPrice.plannerInput input contract available budget history records).length + 1)^3 + 7 := by
  let data := PSTRTablePlannerStreams.firstData input contract available budget history
  let recordData := records.map Datum.natural
  let recordBits := encode recordData
  obtain ⟨digits,firstTrace,firstFinal,firstRun,firstTape,_head,_right,value,width,firstTime,_space⟩ :=
    actual_original_planner_first input contract available budget history records
  let archive := PSTRSymbolicRawStack.archiveLeft data digits
  have firstPhysical : firstFinal.Tape = Tape.mk₂ archive (true :: recordBits) := by
    rw [firstTape]
    rfl
  have firstActual : RunsFrom rawLoopMachine
      ⟨0,Tape.mk₁ (CompactPrice.plannerInput input contract available budget history records)⟩ firstTrace firstFinal :=
    ⟨firstRun.1,firstRun.2.1,firstRun.2.2.1,firstRun.2.2.2.1⟩
  have guardRun := second_guard_runsFrom archive recordBits
  have recordDomain : recordData = [] ∨ 4 ≤ recordData.length := by
    rcases domain with empty | large
    · left
      simp only [recordData,empty,List.map_nil]
    · right
      simpa only [recordData,List.length_map] using large
  obtain ⟨gateTrace,gateRun,_reach,gateLength,_moves,_positions,_cells⟩ :=
    PSTRTML01RecordGate251.actual_records_entry (false :: archive) recordData [] recordDomain
  have gateInitial : PSTRTML01RecordGate251.state 0 (false :: archive) (encode recordData ++ []) =
      (⟨0,Tape.mk₂ (false :: archive) recordBits⟩ : MachineState 4) := by
    simp only [PSTRTML01RecordGate251.state,List.append_nil]
    rfl
  rw [gateInitial] at gateRun
  let firstPart := nativePart dualCode rawLoopMachine Label.first (fun _ => .guard 0)
    (by intro q bit; rfl) _ _ _ firstActual
  let guardPart := nativePart dualCode secondGuardMachine Label.guard (fun _ => .gate 0)
    (by intro q bit; rfl) _ _ _ guardRun
  let gatePart := nativePart dualCode PSTRTML01RecordGate251.gateMachine Label.gate gateFinish
    (by intro q bit; rfl) _ _ _ gateRun
  have bridgeFirst : TM0.step dualCode (tagCfg Label.first firstFinal) =
      some (tagCfg Label.guard (⟨0,Tape.mk₂ archive (true :: recordBits)⟩ : MachineState 2)) := by
    simpa only [tagCfg,firstPhysical] using first_return firstFinal firstActual.2.2.2
  have bridgeGuard : TM0.step dualCode
      (tagCfg Label.guard (⟨2,Tape.mk₂ (false :: archive) recordBits⟩ : MachineState 2)) =
      some (tagCfg Label.gate (⟨0,Tape.mk₂ (false :: archive) recordBits⟩ : MachineState 4)) :=
    guard_return _ guardRun.2.2.2
  let all := (firstPart.append guardPart bridgeFirst).append gatePart bridgeGuard
  have head : all.trace.head? = some
      (TM0.init (CompactPrice.plannerInput input contract available budget history records)) := all.head
  have firstLength : firstPart.trace.length = firstTrace.length := List.length_map _
  have guardLength : guardPart.trace.length = 3 :=
    (List.length_map _).trans (second_guard_length archive recordBits)
  have lastLength : gatePart.trace.length = gateTrace.length := List.length_map _
  have gateBound : gateTrace.length ≤ 4 := by
    rw [gateLength]
    split <;> omega
  refine ⟨digits,all.trace,head,all.chain,all.last,value,width,?_⟩
  simp only [all,RunPart.append_length,firstLength,guardLength,lastLength]
  omega

theorem gate_end_next (data : List Datum) (digits : List Bool) (records : List Nat) :
    TM0.step dualCode (gateEnd data digits records) = some
      ⟨gateFinish (PSTRTML01RecordGate251.final (false :: PSTRSymbolicRawStack.archiveLeft data digits)
        (records.map Datum.natural) []).q,(gateEnd data digits records).Tape⟩ := by
  unfold gateEnd
  apply gate_return
  unfold PSTRTML01RecordGate251.final
  split <;> rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream
