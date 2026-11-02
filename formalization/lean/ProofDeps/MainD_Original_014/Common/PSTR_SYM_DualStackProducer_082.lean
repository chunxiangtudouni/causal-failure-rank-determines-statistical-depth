module

public import Common.PSTR_SYM_PlannerRecordsRun_081

/-! ORIGINAL same-history two-stream input -> genuine two-stack caller.
The terminal head-bit push and gotoReturn are real charged steps. This
does not infer an original Bool-to-track bootstrap or finite empty work
stacks from a quotient Tape equality. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStack

open PaperProofs.Common PaperProofs.Common.Native Turing PSTRTMIncrement009 PSTRQueryRecords
open PSTRWordVM PSTRSymbolicDualStream

abbrev Store := VirtualBool.OldStore (states := dualSupport.card)
abbrev State (C : Type*) := VirtualReturn.State C Store
abbrev Statement (C : Type*) := VirtualReturn.Statement C Store

noncomputable def source : Unit → VirtualReturn.SmallStatement Store := VirtualBool.source dualMachine

noncomputable def program {C : Type*} (caller : Statement C) : Fin 2 → Statement C :=
  VirtualReturn.program source caller

theorem actual_dual_stack {C : Type*} {I : Instance}
    (caller : Statement C) (context : C) (background : Fin 16 → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (available : Finset I.Tool)
    (budget : Rat) (history : List (VisibleEvent I)) :
    ∃ (firstDigits secondDigits : List Bool) (path : List (State C)) (final : State C),
      path.head? = some (VirtualReturn.configuration context background
        (TM2.init (Γ := PSTRWordBool.PushPop.Alphabet) (Λ := Unit) (σ := Store) 0
          (CompactPrice.plannerInput input contract available budget history (nativeRecords available history)))) ∧
      path.IsChain (fun before after => TM2.step (program caller) before = some after) ∧
      path.getLast? = some final ∧ final.l = some 1 ∧
      (VirtualBool.representedState final).Tape = recordEndTape
        (PSTRTablePlannerStreams.firstData input contract available budget history)
        firstDigits (nativeRecords available history) secondDigits ∧
      ListBlank.mk (final.stk 0) = ListBlank.mk [true] ∧
      valueDigits firstDigits = 0 ∧ 3 ≤ firstDigits.length ∧ valueDigits secondDigits = 0 ∧
      path.length ≤ 16385 * ((CompactPrice.plannerInput input contract available budget history
        (nativeRecords available history)).length + 1)^3 ∧
      (∀ current ∈ path, current.var.1 = context ∧
        ∀ slot, slot ≠ 0 → slot ≠ 1 → current.stk slot = background slot) ∧
      ∀ current ∈ path, VirtualReturn.occupiedSlots current.stk ≤ VirtualReturn.outside background +
        65536 * ((CompactPrice.plannerInput input contract available budget history
          (nativeRecords available history)).length + 1)^3 := by
  obtain ⟨firstDigits,secondDigits,oldTrace,oldFinal,actual,oldTape,_head,_right,
    value,width,endValue,time,space⟩ := actual_native_records input contract available budget history
  let bits := CompactPrice.plannerInput input contract available budget history (nativeRecords available history)
  obtain ⟨path,final,first,chain,last,returned,represented,_order,length,_context,frames,mass⟩ :=
    VirtualBool.same_old_run dualMachine caller context background bits oldTrace oldFinal
      actual.1 actual.2.1 actual.2.2.1 actual.2.2.2.1
  have tape : (VirtualBool.representedState final).Tape = recordEndTape
      (PSTRTablePlannerStreams.firstData input contract available budget history)
        firstDigits (nativeRecords available history) secondDigits := by
    rw [represented]
    exact oldTape
  have representedRight : (VirtualBool.representedState final).Tape.right₀ = ListBlank.mk (final.stk 0) :=
    Tape.mk'_right₀ _ _
  have right := congrArg Tape.right₀ tape
  rw [representedRight,record_end_right₀] at right
  have wholeSpace := space oldTrace.length
  simp only [List.take_length] at wholeSpace
  have cubePositive : 1 ≤ (bits.length + 1)^3 := by
    nlinarith [Nat.zero_le (bits.length^2),Nat.zero_le (bits.length^3)]
  refine ⟨firstDigits,secondDigits,path,final,first,chain,last,returned,tape,right,value,width,endValue,?_,frames,?_⟩
  · rw [length]
    change oldTrace.length ≤ 16384 * (bits.length + 1)^3 at time
    change oldTrace.length + 1 ≤ 16385 * (bits.length + 1)^3
    omega
  · intro current present
    exact (mass current present).trans (Nat.add_le_add_left wholeSpace _)

theorem body_at_entry {C : Type*} (caller : Statement C) :
    program caller 0 = VirtualReturn.statement (source ()) := rfl

theorem source_actions : PSTRWordBool.ScannerClock.actions
    (VirtualReturn.statement (C := Unit) (source ())) = 4 := VirtualBool.actions dualMachine

theorem source_pushes : PSTRWordBool.AuxWorkspace.pushes
    (VirtualReturn.statement (C := Unit) (source ())) = 2 := VirtualBool.pushes dualMachine

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStack
