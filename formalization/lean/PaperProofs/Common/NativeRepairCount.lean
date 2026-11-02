module

public import PaperProofs.Common.NativeCostBound

/-!
The number of actual physical executions, on all paths. Pending commitments
and virtual obligations are absent. Counts and expectations stay in ENNReal;
the one-use-tool bound proves finiteness before a real mean is defined.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

noncomputable def runRepairCount (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) : ℝ≥0∞ :=
  ⨆ n, ((run input C mode accounting rule sample n).ledger.executions.length : ℝ≥0∞)

theorem runRepairCount_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World) :
    runRepairCount input C mode accounting rule sample ≤ (min I.stageCount I.toolCount : ℕ) := by
  apply iSup_le
  intro n
  exact_mod_cast run_actualCorrections_le input C mode accounting rule hlegal sample n

section Measurable

variable [MeasurableSpace Seed]

theorem measurable_runRepairCount (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hm : MeasurableRule rule) : Measurable (runRepairCount input C mode accounting rule) := by
  apply Measurable.iSup
  intro n
  exact (measurable_of_countable (fun state : State I => (state.ledger.executions.length : ℝ≥0∞))).comp
    (measurable_run input C mode accounting rule hm n)

noncomputable def expectedRepairCount (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (ν : Measure Seed) :
    ℝ≥0∞ :=
  ∫⁻ sample, runRepairCount input C mode accounting rule sample ∂input.seededWorldLaw ν

theorem expectedRepairCount_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    expectedRepairCount input C mode accounting rule ν ≤ (min I.stageCount I.toolCount : ℕ) := by
  have h := lintegral_mono (μ := input.seededWorldLaw ν) (runRepairCount_le input C mode accounting rule hlegal)
  simpa only [expectedRepairCount, lintegral_const, measure_univ, mul_one] using h

theorem expectedRepairCount_ne_top (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    expectedRepairCount input C mode accounting rule ν ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (expectedRepairCount_le input C mode accounting rule hlegal ν)

noncomputable def meanRepairCount (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (ν : Measure Seed) : ℝ :=
  (expectedRepairCount input C mode accounting rule ν).toReal

theorem ofReal_meanRepairCount (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ENNReal.ofReal (meanRepairCount input C mode accounting rule ν) =
      expectedRepairCount input C mode accounting rule ν :=
  ENNReal.ofReal_toReal (expectedRepairCount_ne_top input C mode accounting rule hlegal ν)

end Measurable

end PaperProofs.Common.Native
