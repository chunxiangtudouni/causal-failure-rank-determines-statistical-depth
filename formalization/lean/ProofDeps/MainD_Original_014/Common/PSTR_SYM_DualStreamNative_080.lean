module

public import Common.PSTR_SYM_DualStreamSource_079

/-! ONE finite native Bool program on the ORIGINAL two-stream planner
input, including the genuine zero-record branch. The semantic record
domain is discharged by the original record producer, not by changing
the caller/input. The output here is staged data, not a planner answer. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream

open PaperProofs.Common Turing PSTRSymbolicRelabel PSTRTMIncrement009

def dualSupport : Finset Label := Finset.univ

noncomputable def dualMachine : Machine dualSupport.card := finiteMachine dualCode dualSupport

theorem dual_supports : TM0.Supports dualCode (dualSupport : Set Label) := by
  simpa only [dualSupport,Finset.coe_univ] using TM0.univ_supports dualCode

theorem record_end_head (data : List Datum) (firstDigits : List Bool) (records : List Nat)
    (secondDigits : List Bool) : (recordEndTape data firstDigits records secondDigits).head = true := by
  unfold recordEndTape
  split <;> rfl

theorem record_end_right (data : List Datum) (firstDigits : List Bool) (records : List Nat)
    (secondDigits : List Bool) : (recordEndTape data firstDigits records secondDigits).right = ListBlank.mk [] := by
  unfold recordEndTape
  split <;> rfl

theorem actual_original_dual {I : Instance} (input : StatisticalInput I) (contract : Contract I)
    (available : Finset I.Tool) (budget : Rat) (history : List (VisibleEvent I)) (records : List Nat)
    (domain : records = [] ∨ 4 ≤ records.length) :
    ∃ (firstDigits secondDigits : List Bool)
      (trace : List (MachineState dualSupport.card)) (final : MachineState dualSupport.card),
      Runs dualMachine (CompactPrice.plannerInput input contract available budget history records) trace final ∧
      final.Tape = recordEndTape (PSTRTablePlannerStreams.firstData input contract available budget history)
        firstDigits records secondDigits ∧
      final.Tape.head = true ∧ final.Tape.right = ListBlank.mk [] ∧
      valueDigits firstDigits = 0 ∧ 3 ≤ firstDigits.length ∧ valueDigits secondDigits = 0 ∧
      trace.length ≤ 16384 * ((CompactPrice.plannerInput input contract available budget history records).length + 1)^3 ∧
      ∀ clock, visitedSpace dualMachine (CompactPrice.plannerInput input contract available budget history records).length
        (trace.take clock) ≤ 65536 * ((CompactPrice.plannerInput input contract available budget history records).length + 1)^3 := by
  obtain ⟨firstDigits,secondDigits,oldTrace,oldFinal,first,chain,last,halt,tape,value,width,endValue,time⟩ :=
    actual_original_dual_source input contract available budget history records domain
  let bits := CompactPrice.plannerInput input contract available budget history records
  let trace := oldTrace.map (relabelCfg (finiteLabels dualSupport))
  let final := relabelCfg (finiteLabels dualSupport) oldFinal
  have actual := finite_runs dualCode dualSupport dual_supports bits oldTrace oldFinal first chain last halt
  have finalTape : final.Tape = recordEndTape
      (PSTRTablePlannerStreams.firstData input contract available budget history) firstDigits records secondDigits := tape
  have length : trace.length = oldTrace.length := List.length_map _
  have sizeRoom : bits.length + 1 ≤ (bits.length + 1)^3 := by
    nlinarith [Nat.zero_le (bits.length^2),Nat.zero_le (bits.length^3)]
  refine ⟨firstDigits,secondDigits,trace,final,actual,finalTape,?_,?_,value,width,endValue,?_,?_⟩
  · rw [finalTape]
    exact record_end_head _ _ _ _
  · rw [finalTape]
    exact record_end_right _ _ _ _
  · rw [length]
    exact time
  · intro clock
    have cells := PSTRTMTrace002.visitedSpace_le dualMachine bits.length (trace.take clock)
    have prefixLength : (trace.take clock).length ≤ oldTrace.length := by
      simp only [List.length_take,length]
      omega
    change oldTrace.length ≤ 16384 * (bits.length + 1)^3 at time
    change visitedSpace dualMachine bits.length (trace.take clock) ≤ 65536 * (bits.length + 1)^3
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStream
