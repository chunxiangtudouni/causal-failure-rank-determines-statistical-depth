module

public import PaperProofs.Retained.PRet_EntryRun_057
public import PaperProofs.Common.ReferenceSuffixRun

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryCharges058

open Common Common.Native PRetEntryInvariant050 PRetEntryRun057

open scoped ENNReal

variable {I : Instance}

/-- Exact observation bill at every reached fresh prefix, before taking any
suprema or conditioning on success. Original future reviews are genuinely
those of the full source interpreter. -/
theorem prefix_observationBill {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (first start : ℕ) (startup : Startup I)
    (target : State (I.freshSuffix first))
    (hi : EntryInvariant input C mode accounting source sample first start startup target) :
    ∃ oldClock ≥ start, target.ledger.observationBill (input.freshSuffix first).fees =
      ∑ stage ∈ Finset.univ.filter (fun stage : I.Stage => first ≤ stage.val),
        ENNReal.ofReal (input.fees.observation stage : ℝ) *
          ((run input C mode accounting source sample oldClock).ledger.reviews stage : ℝ≥0∞) := by
  classical
  obtain ⟨packets, oldClock, hclock, hinfo, hreplay, hr, hw⟩ := hi
  refine ⟨oldClock, hclock, ?_⟩
  rw [Finset.sum_filter, sum_referenceSuffix_stages]
  unfold Ledger.observationBill
  apply Finset.sum_congr rfl
  intro stage _
  have hfee : (input.freshSuffix first).fees.observation stage =
      input.fees.observation (I.freshStageLift first stage) :=
    congrArg Statistics.BinaryExperiment.observationFee (input.freshSuffix_experiment first stage)
  rw [hfee, hr]

/-- All-path domination of the true fresh observation objective. This
includes nonreturned paths and infinite review bills; no finite expectation
or source-success hypothesis is used. -/
theorem run_observationBill_le {Seed : Type*} [MeasurableSpace Seed] (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (mode : ResourceMode)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hsource : MeasurableRule source) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample) :
    runObservationBill (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first))
      (PRetFreshExtractionPolicy047.rule first accounting source
        (publicStartup (run input C mode accounting source sample start)))
      (sample.1, input.restrictFreshWorld first sample.2) ≤
      runFutureObservationBill input C mode accounting source first sample := by
  apply iSup_le
  intro n
  have hi := run_entryInvariant input C hearly mode accounting source hsource hlegal sample first start hentry n
  obtain ⟨oldClock, _, hbill⟩ := prefix_observationBill input C mode accounting source sample first start _ _ hi
  rw [hbill]
  exact le_iSup (fun oldClock => ∑ stage ∈ Finset.univ.filter (fun stage : I.Stage => first ≤ stage.val),
    ENNReal.ofReal (input.fees.observation stage : ℝ) *
      ((run input C mode accounting source sample oldClock).ledger.reviews stage : ℝ≥0∞)) oldClock

end PaperProofs.Retained.PRetEntryCharges058

