module

public import PaperProofs.Retained.PRet_AmbientJoint_071
public import PaperProofs.Retained.PRet_EntryCompletion_062

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetAmbientSuccess072

open Common Common.Native PRetAmbientJoint071 PRetEntryCompletion062

variable {I Ambient : Instance}

/-- Genuine completion and ambient old-H matching are transported together
from a complete comparator which need NOT satisfy physical native success.
This is the actual predicate transport for nested fresh continuations. -/
theorem completed_matching_transport {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hm : MeasurableRule source) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample)
    (embed : I.Stage → Ambient.Stage) (base old : Finset Ambient.Stage)
    (hold : old ⊆ base ∪ (ordinaryMismatches (run input C mode accounting source sample start).ledger).image embed)
    (hsuccess : ∃ last, (run input C mode accounting source sample last).halted = true ∧
      (run input C mode accounting source sample last).ledger.finished = true ∧
      (run input C mode accounting source sample last).ledger.abandoned = false ∧
      Matchable Ambient (base ∪ (ordinaryMismatches (run input C mode accounting source sample last).ledger).image embed)) :
    ∃ n,
      let target := run (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first))
        (PRetFreshExtractionPolicy047.rule first accounting source (publicStartup (run input C mode accounting source sample start)))
        (sample.1, input.restrictFreshWorld first sample.2) n
      target.halted = true ∧ target.ledger.finished = true ∧ target.ledger.abandoned = false ∧
        Matchable Ambient (old ∪ (liftedErrors I first target.ledger).image embed) := by
  obtain ⟨last, hh, hf, ha, hmatch⟩ := hsuccess
  obtain ⟨n, hhalt, hfinished, habandoned⟩ := run_completion input C hearly mode accounting source hm hlegal
    sample first start hentry ⟨last, hh, hf, ha⟩
  exact ⟨n, hhalt, hfinished, habandoned,
    ambient_joint_errors_matchable input C hearly mode accounting source hm hlegal sample first start hentry
      embed base old hold last hh hmatch n⟩

end PaperProofs.Retained.PRetAmbientSuccess072

