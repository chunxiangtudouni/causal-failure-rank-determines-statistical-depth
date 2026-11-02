module

public import PaperProofs.Common.ReferenceObservationCost

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native MeasureTheory
open scoped ENNReal

namespace PDROC.RetainedEnvelopeRun.EntryPartition

variable {I : Instance}

/-- Countable disjoint atoms of the genuine complete first-entry history.
The integrand may be infinite; only missing entries must contribute zero.
This is the policy-parametric form of the original reference entry partition. -/
theorem lintegral_eq_tsum_entry
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Unit)
    (stage : I.Stage) (f : Unit × input.World → ℝ≥0∞) (hf : Measurable f)
    (hzero : ∀ sample, entryHistory input C mode accounting policy.rule stage sample = none →
      f sample = 0) :
    (∫⁻ sample, f sample ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I),
        ∫⁻ sample in {sample | entryHistory input C mode accounting policy.rule stage sample = some history},
          f sample ∂input.seededWorldLaw (Measure.dirac ()) := by
  classical
  let atom := fun history : List (VisibleEvent I) =>
    {sample | entryHistory input C mode accounting policy.rule stage sample = some history}
  have hmeas (history : List (VisibleEvent I)) : MeasurableSet (atom history) :=
    (measurable_entryHistory input C mode accounting policy.rule policy.measurable_rule stage)
      (measurableSet_singleton (some history))
  have hsplit : ∀ sample, f sample = ∑' history : List (VisibleEvent I),
      (atom history).indicator f sample := by
    intro sample
    cases he : entryHistory input C mode accounting policy.rule stage sample with
    | none =>
      rw [hzero sample he]
      symm
      calc
        _ = ∑' _history : List (VisibleEvent I), (0 : ℝ≥0∞) := by
          apply tsum_congr
          intro history
          apply Set.indicator_of_notMem
          intro hh
          have impossible := he.symm.trans hh
          cases impossible
        _ = 0 := tsum_zero
    | some history =>
      symm
      calc
        _ = (atom history).indicator f sample := by
          apply tsum_eq_single history
          intro other hne
          apply Set.indicator_of_notMem
          intro hh
          exact hne (Option.some.inj (hh.symm.trans he))
        _ = f sample := Set.indicator_of_mem (show sample ∈ atom history from he) f
  calc
    _ = ∫⁻ sample, ∑' history : List (VisibleEvent I), (atom history).indicator f sample
          ∂input.seededWorldLaw (Measure.dirac ()) := lintegral_congr hsplit
    _ = ∑' history : List (VisibleEvent I), ∫⁻ sample, (atom history).indicator f sample
          ∂input.seededWorldLaw (Measure.dirac ()) :=
        lintegral_tsum (fun history => (hf.indicator (hmeas history)).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro history
      exact lintegral_indicator (hmeas history) f

end PDROC.RetainedEnvelopeRun.EntryPartition
