module

public import PaperProofs.Retained.PRet_EntryMismatch_063

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetAmbientJoint071

open Common Common.Native PRetEntryInvariant050 PRetEntryRun057 PRetEntryMismatch063

variable {I Ambient : Instance}

/-- The runtime extraction also retains obligations in an AMBIENT original
input. This is the matching interface needed when the source itself is a
fresh comparator, whose old H is absent from its physical fresh ledger.
No physical repairs or native success of that source are required. -/
theorem ambient_joint_errors_matchable {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hm : MeasurableRule source) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample)
    (embed : I.Stage → Ambient.Stage) (base old : Finset Ambient.Stage)
    (hold : old ⊆ base ∪ (ordinaryMismatches (run input C mode accounting source sample start).ledger).image embed)
    (last : ℕ) (hh : (run input C mode accounting source sample last).halted = true)
    (hmatch : Matchable Ambient (base ∪ (ordinaryMismatches (run input C mode accounting source sample last).ledger).image embed))
    (n : ℕ) :
    Matchable Ambient (old ∪ (liftedErrors I first
      (run (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first))
        (PRetFreshExtractionPolicy047.rule first accounting source (publicStartup (run input C mode accounting source sample start)))
        (sample.1, input.restrictFreshWorld first sample.2) n).ledger).image embed) := by
  have htarget := (PRetFreshExtractionPolicy047.policy input first accounting source hm
    (publicStartup (run input C mode accounting source sample start))).legal
  have ht := run_truth (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) _ htarget (sample.1, input.restrictFreshWorld first sample.2) n
  obtain ⟨_, oldClock, _, _, _, _, hw⟩ := run_entryInvariant input C hearly mode accounting source hm hlegal
    sample first start hentry n
  have hfuture := (liftedErrors_subset_source input C mode accounting source hlegal sample first oldClock _ hw ht).trans
    (run_mismatches_subset_halted input C mode accounting source hlegal sample last hh oldClock)
  apply hmatch.subset
  apply Finset.union_subset
  · apply hold.trans
    exact Finset.union_subset_union_right (Finset.image_subset_image
      (run_mismatches_subset_halted input C mode accounting source hlegal sample last hh start))
  · exact (Finset.image_subset_image hfuture).trans (Finset.subset_union_right)

end PaperProofs.Retained.PRetAmbientJoint071

