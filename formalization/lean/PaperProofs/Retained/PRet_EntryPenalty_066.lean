module

public import PaperProofs.Retained.PRet_EntryCharges_058
public import PaperProofs.Retained.PRet_NativeFreshSuccess_064
public import PaperProofs.Retained.PRet_FreshCharge_065

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryPenalty066

open Common Common.Native MeasureTheory PRetEntryCharges058 PRetNativeFreshSuccess064 PRetFreshCharge065

open scoped ENNReal

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def fullCharge (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed) (first : ℕ) (penalty : ℝ≥0∞)
    (sample : Seed × input.World) : ℝ≥0∞ := by
  classical
  exact runFutureObservationBill input C mode accounting source first sample +
    if runSuccess input C mode accounting source sample then 0 else penalty

theorem measurable_futureBill (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed) (hm : MeasurableRule source) (first : ℕ) :
    Measurable (runFutureObservationBill input C mode accounting source first) := by
  classical
  apply Measurable.iSup
  intro n
  exact (measurable_of_countable (fun state : State I =>
    ∑ stage ∈ Finset.univ.filter (fun stage : I.Stage => first ≤ stage.val),
      ENNReal.ofReal (input.fees.observation stage : ℝ) * (state.ledger.reviews stage : ℝ≥0∞))).comp
        (measurable_run input C mode accounting source hm n)

theorem measurable_fullCharge (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed) (hm : MeasurableRule source)
    (first : ℕ) (penalty : ℝ≥0∞) : Measurable (fullCharge input C mode accounting source first penalty) := by
  classical
  exact (measurable_futureBill input C mode accounting source hm first).add
    (Measurable.ite (measurableSet_runSuccess input C mode accounting source hm) measurable_const measurable_const)

/-- One actual eventual-failure penalty and all actual future observations
are preserved on every path, including failure and nonreturn. -/
theorem extraction_charge_le (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hm : MeasurableRule source) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample)
    (old : Finset I.Stage) (hold : reportedErrors I (run input C mode accounting source sample start).history first = old)
    (penalty : ℝ≥0∞) :
    freshCharge input first old (PRetFreshExtractionPolicy047.rule first accounting source
      (publicStartup (run input C mode accounting source sample start))) penalty
        (sample.1, input.restrictFreshWorld first sample.2) ≤ fullCharge input C mode accounting source first penalty sample := by
  classical
  apply add_le_add (run_observationBill_le input C hearly mode accounting source hm hlegal sample first start hentry)
  by_cases hs : runSuccess input C mode accounting source sample
  · have hf := freshSuccess_of_nativeSuccess input C hearly mode accounting source hm hlegal sample first start hentry old hold hs
    simp only [hs, hf, ↓reduceIte, le_refl]
  · simp only [hs, ↓reduceIte]
    split_ifs
    · exact bot_le
    · exact le_rfl

end PaperProofs.Retained.PRetEntryPenalty066




