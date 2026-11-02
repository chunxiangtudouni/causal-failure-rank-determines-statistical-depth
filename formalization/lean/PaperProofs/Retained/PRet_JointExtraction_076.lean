module

public import PaperProofs.Retained.PRet_AmbientSuccess_072
public import PaperProofs.Retained.PRet_JointCharges_075
public import PaperProofs.Retained.PRet_EntryCharges_058

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetJointExtraction076

open Common Common.Native MeasureTheory PRetAmbientComparator073 PRetAmbientSuccess072 PRetJointCharges075
open PRetEntryCharges058
open scoped ENNReal

variable {Physical Ambient : Instance} {Seed : Type*}

theorem jointSuccess_transport [MeasurableSpace Seed] (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Seed)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule first start sample)
    (embed : Physical.Stage → Ambient.Stage) (base old : Finset Ambient.Stage)
    (hold : old ⊆ base ∪ (ordinaryMismatches
      (run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule sample start).ledger).image embed)
    (hs : jointSuccess input embed base source.rule sample) :
    jointSuccess (input.freshSuffix first)
      (fun stage => embed (Physical.freshStageLift first stage)) old
      (PRetFreshExtractionPolicy047.rule first (zeroNormalAccounting Physical) source.rule
        (publicStartup (run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule sample start)))
      (sample.1, input.restrictFreshWorld first sample.2) := by
  obtain ⟨n, hh, hf, ha, hm⟩ := completed_matching_transport input (freshContract Physical) rfl .uncapped
    (zeroNormalAccounting Physical) source.rule source.measurable_rule source.legal sample first start hentry embed base old hold hs
  refine ⟨n, hh, hf, ha, ?_⟩
  simpa only [liftedErrors, Finset.image_image, Function.comp_def] using hm

noncomputable def futureJointCharge (input : StatisticalInput Physical)
    (embed : Physical.Stage → Ambient.Stage) (base : Finset Ambient.Stage)
    (rule : PolicyRule Physical Seed) (first : ℕ) (penalty : ℝ≥0∞)
    (sample : Seed × input.World) : ℝ≥0∞ := by
  classical
  exact runFutureObservationBill input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) rule first sample +
    if jointSuccess input embed base rule sample then 0 else penalty

/-- Actual nested-fresh comparison with the ambient source-success
predicate, including all source-failure/nonreturn paths and infinity. -/
theorem jointCharge_le_future [MeasurableSpace Seed] (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Seed)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule first start sample)
    (embed : Physical.Stage → Ambient.Stage) (base old : Finset Ambient.Stage)
    (hold : old ⊆ base ∪ (ordinaryMismatches
      (run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule sample start).ledger).image embed)
    (penalty : ℝ≥0∞) :
    jointCharge (input.freshSuffix first) (fun stage => embed (Physical.freshStageLift first stage)) old
      (PRetFreshExtractionPolicy047.rule first (zeroNormalAccounting Physical) source.rule
        (publicStartup (run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule sample start))) penalty
      (sample.1, input.restrictFreshWorld first sample.2) ≤
      futureJointCharge input embed base source.rule first penalty sample := by
  classical
  apply add_le_add (run_observationBill_le input (freshContract Physical) rfl .uncapped (zeroNormalAccounting Physical)
    source.rule source.measurable_rule source.legal sample first start hentry)
  by_cases hs : jointSuccess input embed base source.rule sample
  · have ht := jointSuccess_transport input source sample first start hentry embed base old hold hs
    simp only [hs, ht, ↓reduceIte, le_refl]
  · simp only [hs, ↓reduceIte]
    split_ifs
    · exact bot_le
    · exact le_rfl

end PaperProofs.Retained.PRetJointExtraction076


