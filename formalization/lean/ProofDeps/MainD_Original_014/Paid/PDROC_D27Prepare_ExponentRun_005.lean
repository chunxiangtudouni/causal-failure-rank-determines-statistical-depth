module

public import Paid.PDROC_D27Prepare_ExponentRun_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.ExponentRun

/-- The original page7 setup and all page8/9 iterations compute E and the
exponent threshold from the actual raw/M boundary, ending at original pc10. -/
theorem original_E_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (initial : ExponentInitial P fee before) (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State,QInitial P fee after ∧
      Segment region input before after 64 (operandBudget P fee) (40*(P.certificate.E+1)) := by
  obtain ⟨initialized,initMatch,initPc,initData,initSegment⟩ := setup_segment P fee input before initial bounded
  have positive : 1≤P.certificate.E := Search.exponent_initial_le P.certificate
  obtain ⟨after,finalMemory,afterMatch,afterData,afterPc,loopSegment⟩ :=
    loop_segment P fee input (P.certificate.E-1) 1 initialized
      (setupMemory P (Search.currentMemory before)) (by omega) le_rfl initMatch initPc
      initSegment.final_bounds initData
  have whole := initSegment.trans loopSegment
  have finalBoundary := finish_of_progress P fee before after initial whole.final_frame afterPc whole.fresh
    (match_has after finalMemory 8 _ afterMatch afterData.counter)
    (match_has after finalMemory 31 _ afterMatch afterData.threshold)
  exact ⟨after,finalBoundary,whole.weaken_budget (by omega)⟩

end PDROC.D27Prepare.ExponentRun
