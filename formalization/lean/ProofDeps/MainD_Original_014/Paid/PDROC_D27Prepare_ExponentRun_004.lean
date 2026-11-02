module

public import Paid.PDROC_D27Prepare_ExponentRun_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.ExponentRun

/-- Actual increasing E loop. The logical fuel proves termination of the
literal controller; the machine reads only its current counter and power. -/
theorem loop_segment (P : Parameters) (fee : ℚ) (input : List Cell) :
    ∀ fuel e (before : State) (memory : SlotMemory),e+fuel=P.certificate.E → 1≤e →
      MemoryMatch before memory → before.pc=pc 8 →
      StateBounds 64 (operandBudget P fee) before → ExponentData P memory e →
      ∃ (after : State) (finalMemory : SlotMemory),MemoryMatch after finalMemory ∧
        ExponentData P finalMemory P.certificate.E ∧ after.pc=pc 10 ∧
        Segment region input before after 64 (operandBudget P fee) (31*fuel+9) := by
  intro fuel
  induction fuel with
  | zero =>
    intro e before memory fits positive matched location bounded data
    have equal : e=P.certificate.E := by omega
    subst e
    obtain ⟨after,afterMatch,afterPc,segment⟩ :=
      guard_segment P fee input before memory P.certificate.E matched location bounded positive le_rfl data
    simp only at afterPc
    exact ⟨after,memory,afterMatch,data,afterPc,by simpa using segment⟩
  | succ fuel ih =>
    intro e before memory fits positive matched location bounded data
    have range : e<P.certificate.E := by omega
    have different : e≠P.certificate.E := by omega
    obtain ⟨guarded,guardMatch,guardPc,guardSegment⟩ :=
      guard_segment P fee input before memory e matched location bounded positive range.le data
    rw [ite_eq_right different] at guardPc
    obtain ⟨middle,middleMatch,middlePc,stepSegment⟩ :=
      step_segment P fee input guarded memory e guardMatch guardPc guardSegment.final_bounds range data
    obtain ⟨after,finalMemory,afterMatch,afterData,afterPc,later⟩ :=
      ih (e+1) middle (stepMemory memory e) (by omega) (by omega) middleMatch middlePc
        stepSegment.final_bounds (step_data P memory e data)
    exact ⟨after,finalMemory,afterMatch,afterData,afterPc,
      ((guardSegment.trans stepSegment).trans later).weaken_budget (by omega)⟩

end PDROC.D27Prepare.ExponentRun
