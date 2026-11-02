module

public import Common.PSTR_SYM_DualStackProducer_082

/-! SAME actual dual-parser path, including resources inside its TM2
statement. The active caller1 is not executed by this callee path; its
arbitrary code is never charged as if it were parser code. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStack

open PaperProofs.Common PaperProofs.Common.Native Turing PSTRTMIncrement009 PSTRQueryRecords
open PSTRWordVM PSTRSymbolicDualStream

def workStacks {C : Type*} (state : State C) : VirtualReturn.SmallStack → List Bool :=
  fun slot => state.stk (VirtualReturn.role slot)

theorem rebuild_slots {C : Type*} (state : State C) (background : Fin 16 → List Bool)
    (frame : ∀ slot, slot ≠ 0 → slot ≠ 1 → state.stk slot = background slot) :
    VirtualReturn.slots background (workStacks state) = state.stk := by
  funext slot
  by_cases zero : slot = 0
  · subst slot; rfl
  by_cases one : slot = 1
  · subst slot; rfl
  rw [VirtualReturn.slots_frame background (workStacks state) slot zero one]
  exact (frame slot zero one).symm

theorem work_mass {C : Type*} (state : State C) (background : Fin 16 → List Bool) (budget : Nat)
    (frame : ∀ slot, slot ≠ 0 → slot ≠ 1 → state.stk slot = background slot)
    (mass : VirtualReturn.occupiedSlots state.stk ≤ VirtualReturn.outside background + budget) :
    (state.stk 0).length + (state.stk 1).length ≤ budget := by
  have partition := VirtualReturn.occupied_slots background (workStacks state)
  rw [rebuild_slots state background frame] at partition
  change VirtualReturn.occupiedSlots state.stk =
    VirtualReturn.outside background + (state.stk 0).length + (state.stk 1).length at partition
  omega

theorem actual_node_resources {C : Type*} (state : State C) (context : C)
    (background : Fin 16 → List Bool) (budget : Nat)
    (sameContext : state.var.1 = context)
    (frame : ∀ slot, slot ≠ 0 → slot ≠ 1 → state.stk slot = background slot)
    (mass : VirtualReturn.occupiedSlots state.stk ≤ VirtualReturn.outside background + budget) :
    ∀ node ∈ PSTRWordBool.AuxWorkspace.nodes (VirtualReturn.statement (source ())) state.var state.stk,
      node.1.1 = context ∧ (∀ slot, slot ≠ 0 → slot ≠ 1 → node.2 slot = background slot) ∧
      VirtualReturn.occupiedSlots node.2 ≤ VirtualReturn.outside background + 2 * budget + 4 := by
  have resources := VirtualBool.internal_resources dualMachine state.var.1 state.var.2 (workStacks state) background
  rw [rebuild_slots state background frame] at resources
  have memory : (state.var.1,state.var.2) = state.var := Prod.eta state.var
  rw [memory] at resources
  have work := work_mass state background budget frame mass
  intro node present
  obtain ⟨keptContext,keptFrame,cells⟩ := resources node present
  refine ⟨keptContext.trans sameContext,keptFrame,?_⟩
  change VirtualReturn.occupiedSlots node.2 ≤ VirtualReturn.outside background +
    2 * ((state.stk 0).length + (state.stk 1).length + 2) at cells
  omega

theorem actual_dual_stack_resources {C : Type*} {I : Instance}
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
      (∀ current ∈ path, VirtualReturn.occupiedSlots current.stk ≤ VirtualReturn.outside background +
        65536 * ((CompactPrice.plannerInput input contract available budget history
          (nativeRecords available history)).length + 1)^3) ∧
      ∀ current ∈ path, current.l = some 0 →
        ∀ node ∈ PSTRWordBool.AuxWorkspace.nodes (program caller 0) current.var current.stk,
          node.1.1 = context ∧ (∀ slot, slot ≠ 0 → slot ≠ 1 → node.2 slot = background slot) ∧
          VirtualReturn.occupiedSlots node.2 ≤ VirtualReturn.outside background +
            131072 * ((CompactPrice.plannerInput input contract available budget history
              (nativeRecords available history)).length + 1)^3 + 4 := by
  obtain ⟨firstDigits,secondDigits,path,final,first,chain,last,returned,tape,right,
    value,width,endValue,time,frame,mass⟩ := actual_dual_stack caller context background input contract available budget history
  refine ⟨firstDigits,secondDigits,path,final,first,chain,last,returned,tape,right,
    value,width,endValue,time,frame,mass,?_⟩
  intro current present _active node member
  rw [body_at_entry] at member
  have nodes := actual_node_resources current context background
    (65536 * ((CompactPrice.plannerInput input contract available budget history
      (nativeRecords available history)).length + 1)^3)
    (frame current present).1 (frame current present).2 (mass current present) node member
  refine ⟨nodes.1,nodes.2.1,?_⟩
  exact nodes.2.2.trans (by omega)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDualStack
