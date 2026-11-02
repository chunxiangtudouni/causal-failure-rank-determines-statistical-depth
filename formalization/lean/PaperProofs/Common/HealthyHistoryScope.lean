module

public import PaperProofs.Common.HistorySuffixBridge

/-!
The literal temporal scope of the ARCHIVED 2026-10-27 price-proofs.tex:77--90.
Earlier obligations can be healthy after CURRENT-stage observations. This
broad target keeps the original fresh prior and is refuted by the native
counterexamples in HealthyHistoryCounterexample/HealthyPrewriteCounterexample.

On 2026-10-29 the user approved restricting the paper's B09 claim to first
entry. Its authoritative positive statement and proof are the existing
HealthyStageEntryHistoryPenaltyBridge and healthyStageEntryHistoryPenaltyBridge
in HistorySuffixBridge. This legacy broad Prop is retained for traceability;
it is neither an axiom nor an assumption of that proof, and is not silently
redefined to make the old negative results disappear.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

universe uScope

/-- Literal all-healthy-history reading of the archived bridge: previous
obligations are truly viable and the current cursor is i, but reviews on i
are not silently required to be zero. R is the exact unused-tool set from
the actual fixed public snapshot. All original seed/policy gates remain.
This broad target is NOT an assumption of any proved first-entry theorem. -/
def AllHealthyHistoryPenaltyBridge (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I), C.IsCurrentAllocation →
    ∀ (accounting : NormalAccounting I) (Seed : Type uScope) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (policy : Policy input C .native accounting Seed) (ν : Measure Seed),
        IsProbabilityMeasure ν →
        ∀ (next n : ℕ) (_hnext : next ≤ I.stageCount) (startup : Startup I)
          (gate : Set Seed), MeasurableSet gate →
          (∀ sample ∈ historyGate input C .native accounting policy.rule n startup gate,
            (run input C .native accounting policy.rule sample n).cursor = next ∧
              DeadlineViableBefore C (run input C .native accounting policy.rule sample n) next) →
          ∀ penalty : ℝ≥0∞,
            input.healthyPenalty next startup.availableTools penalty *
                input.seededWorldLaw ν (historyGate input C .native accounting policy.rule n startup gate) ≤
              ∫⁻ sample in historyGate input C .native accounting policy.rule n startup gate,
                historyComparisonCharge input C .native accounting policy.rule n penalty sample
                  ∂input.seededWorldLaw ν

/-- Only this direction is automatic. The converse would discard the
unproved difference between a fresh stage prior and a current posterior. -/
theorem AllHealthyHistoryPenaltyBridge.firstEntry_projection (input : StatisticalInput I)
    (hbridge : AllHealthyHistoryPenaltyBridge.{uScope} input) :
    HealthyStageEntryHistoryPenaltyBridge.{uScope} input := by
  intro C hC accounting Seed m
  let : MeasurableSpace Seed := m
  intro policy ν hν next n hnext startup gate hgate hentry penalty
  apply hbridge C hC accounting Seed m policy ν hν next n hnext startup gate hgate ?_ penalty
  intro sample hs
  obtain ⟨hfirst, hhealthy⟩ := hentry sample hs
  exact ⟨hfirst.1, hhealthy⟩

end PaperProofs.Common.Native
