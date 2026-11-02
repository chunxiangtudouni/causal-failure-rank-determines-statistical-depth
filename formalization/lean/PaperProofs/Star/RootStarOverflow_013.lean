module

public import PaperProofs.Star.RootStarOverflow_012
public import PaperProofs.Star.PDROC_StarFirstExit_Local_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

/-- The original overflow assembly, using the real entry and real first exit
of the actual ideal run, with no supplied identification premise. -/
theorem starOverflowAssembly (P : Parameters) : P.StarOverflowAssembly := by
  apply starOverflowAssembly_of_identification P
  intro order kind C hC accounting r _hr _hquarter quota sample clock stage active selected reached
  have legal := star_legal_uncapped (Seed := Unit) P order kind r none C hC accounting
  obtain ⟨length, _, hp⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) legal sample clock
  obtain ⟨next, step⟩ := legal sample.1 ((P.input order).truthAt sample.2)
    (worldTapes (P.input order) sample.2) length _ hp active
  have selected' : P.starReferenceRule order kind r none sample.1
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history = .review stage := selected
  rw [selected'] at step
  cases step with
  | review _ live port _ =>
    apply PDROC.StarFirstExit.Local.review_at_quota_mem_anyStarOverflow P order kind r C accounting
      sample clock stage quota live port selected'
    rw [← prefix_historyObservations_length (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) sample.1 ((P.input order).truthAt sample.2)
      (worldTapes (P.input order) sample.2) hp stage]
    exact_mod_cast reached

end RootStarOverflow
