module

public import PaperProofs.Star.PStarLR_TerminalCriterion_019
public import PaperProofs.Star.PDROC_StarLRHead_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PStarLR

theorem lateRetainedConstruction (P : PaperProofs.Star.Parameters) : P.C09Claims := by
  intro order C late accounting r positive small
  have legal := retained_legal_uncapped P order .lateRetained (by decide) r none C late.2.1 late.2.2 accounting
    (Seed := Unit)
  have complete := PDROC.StarLRHead.original_allWritten_ae P order C late accounting positive small
  have terminal := retained_terminalCriterion_of_ae_allWritten P order .lateRetained (by decide) r C
    late.2.1 late.2.2 accounting complete
  refine ⟨lateReferenceLegality P order r none C late accounting, ?_, ?_, ?_, ?_, terminal, ?_⟩
  · exact PDROC.StarLRHead.original_risk_le_of_terminalCriterion P order C late accounting positive small terminal
  · exact PDROC.StarLRHead.original_expectedObservationBill_le P order C late accounting positive small
  · intro sample n stage nonzero
    exact late_run_other_reviews_zero_of_legal P order r none C .uncapped accounting legal sample n stage nonzero
  · exact retainedNoEarlyCommitment_of_legal P order .lateRetained (by decide) r none C accounting legal
  · exact referenceAllPathCharges_of_legal P order .lateRetained r none C accounting legal

end PStarLR
