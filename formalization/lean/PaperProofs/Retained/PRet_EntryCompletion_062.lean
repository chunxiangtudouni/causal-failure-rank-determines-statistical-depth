module

public import PaperProofs.Retained.PRet_EntryProgress_061
public import PaperProofs.Retained.PRet_EntryHalt_060

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryCompletion062

open Common Common.Native PRetEntryInvariant050 PRetEntryRun057 PRetEntryHalt060 PRetEntryProgress061

variable {I : Instance}

theorem prefix_completion {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample)
    (hcomplete : ∃ last, (run input C mode accounting source sample last).halted = true ∧
      (run input C mode accounting source sample last).ledger.finished = true ∧
      (run input C mode accounting source sample last).ledger.abandoned = false)
    {n : ℕ} {target : State (I.freshSuffix first)}
    (hp : Prefix (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) (PRetFreshExtractionPolicy047.rule first accounting source
        (publicStartup (run input C mode accounting source sample start)))
      sample.1 ((input.freshSuffix first).truthAt (input.restrictFreshWorld first sample.2))
      (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first sample.2)) n target)
    (hh : target.halted = true) : target.ledger.finished = true ∧ target.ledger.abandoned = false := by
  cases hp with
  | initial => cases hh
  | @next n before target earlier step =>
    have hi := prefix_entryInvariant input C hearly mode accounting source hlegal sample first start hentry earlier
    have ha := step_source_active (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) _ step
    obtain ⟨next, hraw, hfinished⟩ := raw_step input C mode accounting source hlegal sample first start hentry hcomplete earlier hi ha
    have hs := PRetRetainedGuard007.guarded_action_of_step (input.freshSuffix first)
      (freshContract (I.freshSuffix first)) rfl (zeroNormalAccounting (I.freshSuffix first))
      (PRetFreshExtractionPolicy047.raw first accounting source (publicStartup (run input C mode accounting source sample start)))
      sample.1 _ _ earlier hraw
    change PRetFreshExtractionPolicy047.rule first accounting source
      (publicStartup (run input C mode accounting source sample start)) sample.1 before.history =
        PRetFreshExtractionPolicy047.raw first accounting source
          (publicStartup (run input C mode accounting source sample start)) sample.1 before.history at hs
    rw [hs] at step
    have heq := step_deterministic (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) _ step hraw
    rw [heq]
    exact hfinished (heq ▸ hh)

/-- Actual extracted completion, valid even when the original completed
source never performed any repairs. Matching is deliberately independent. -/
theorem run_completion {Seed : Type*} [MeasurableSpace Seed] (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (mode : ResourceMode)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hsource : MeasurableRule source) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample)
    (hcomplete : ∃ last, (run input C mode accounting source sample last).halted = true ∧
      (run input C mode accounting source sample last).ledger.finished = true ∧
      (run input C mode accounting source sample last).ledger.abandoned = false) :
    ∃ n,
      let state := run (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first))
        (PRetFreshExtractionPolicy047.rule first accounting source (publicStartup (run input C mode accounting source sample start)))
        (sample.1, input.restrictFreshWorld first sample.2) n
      state.halted = true ∧ state.ledger.finished = true ∧ state.ledger.abandoned = false := by
  obtain ⟨last, hh, hf, ha⟩ := hcomplete
  let bound := (informationTrace (run input C mode accounting source sample last).history).length +
    (I.freshSuffix first).stageCount + 2 * (I.freshSuffix first).toolCount + 2
  have hhalt := halted_of_source_halted input C hearly mode accounting source hsource hlegal sample first start hentry last hh
  change (run (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first))
    (PRetFreshExtractionPolicy047.rule first accounting source (publicStartup (run input C mode accounting source sample start)))
    (sample.1, input.restrictFreshWorld first sample.2) bound).halted = true at hhalt
  have htarget := (PRetFreshExtractionPolicy047.policy input first accounting source hsource
    (publicStartup (run input C mode accounting source sample start))).legal
  obtain ⟨_, _, hp⟩ := run_has_prefix (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first))
    (PRetFreshExtractionPolicy047.rule first accounting source (publicStartup (run input C mode accounting source sample start)))
    htarget (sample.1, input.restrictFreshWorld first sample.2) bound
  exact ⟨bound, hhalt, prefix_completion input C hearly mode accounting source hlegal sample first start hentry
    ⟨last, hh, hf, ha⟩ hp hhalt⟩

end PaperProofs.Retained.PRetEntryCompletion062


