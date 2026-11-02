module

public import PaperProofs.Retained.PRet_EntryCompletion_062
public import PaperProofs.Retained.PRet_EntryMismatch_063
public import PaperProofs.Retained.PRet_ActualReportedErrors_048

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetNativeFreshSuccess064

open Common Common.Native PRetEntryCompletion062 PRetEntryMismatch063 PRetOutputCompletion049
open PRetActualReportedErrors048

variable {I : Instance}

/-- Pathwise native-success transport through the actual extracted fresh
Policy, retaining the exact reported old H. No success/pathwise guarantee is
assumed in the definition or legality of that Policy. -/
theorem freshSuccess_of_nativeSuccess {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hsource : MeasurableRule source) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample)
    (old : Finset I.Stage) (hold : reportedErrors I (run input C mode accounting source sample start).history first = old)
    (hsuccess : runSuccess input C mode accounting source sample) :
    freshSuccess input first old
      (PRetFreshExtractionPolicy047.rule first accounting source (publicStartup (run input C mode accounting source sample start)))
      (sample.1, input.restrictFreshWorld first sample.2) := by
  obtain ⟨last, hh, hgood⟩ := hsuccess
  have hcomplete := nativeSuccess_completed input C mode accounting source sample ⟨last, hh, hgood⟩
  obtain ⟨n, hhalt, hfinished, habandoned⟩ := run_completion input C hearly mode accounting source hsource hlegal
    sample first start hentry hcomplete
  refine ⟨n, hhalt, hfinished, habandoned, ?_⟩
  have hm := run_success_mismatches_matchable input C mode accounting source hlegal sample last hgood
  have hsub : old ⊆ ordinaryMismatches (run input C mode accounting source sample start).ledger := by
    obtain ⟨_, _, hp⟩ := run_has_prefix input C mode accounting source hlegal sample start
    rw [← hold, prefix_reportedErrors input C hearly mode accounting source sample.1 _ _ hp first]
    exact Finset.inter_subset_left
  exact joint_errors_matchable input C hearly mode accounting source hsource hlegal sample first start hentry old
    hsub last hh hm n

end PaperProofs.Retained.PRetNativeFreshSuccess064
