module

public import PaperProofs.Retained.PRet_FreshOldObligation_039
public import PaperProofs.Common.NativeEmpty

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshTerminalBoundary040

open Common Common.Native MeasureTheory
open scoped ENNReal

variable {I : Instance}

theorem freshSuccess_stop_empty {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (next : ℕ) [IsEmpty (I.freshSuffix next).Stage]
    (old : Finset I.Stage) (hmatch : Matchable I old)
    (sample : Seed × (input.freshSuffix next).World) :
    freshSuccess input next old
      (stopPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
        (zeroNormalAccounting (I.freshSuffix next)) Seed).rule sample := by
  obtain ⟨n, hh, hs⟩ := stop_runSuccess_empty (input.freshSuffix next)
    (freshContract (I.freshSuffix next)) .uncapped (zeroNormalAccounting (I.freshSuffix next)) sample
  refine ⟨n, hh, hs.1, hs.2.1, ?_⟩
  let state := run (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
    (zeroNormalAccounting (I.freshSuffix next))
    (stopPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)) Seed).rule sample n
  change Matchable I (old ∪ liftedErrors I next state.ledger)
  have herrors : ordinaryMismatches state.ledger = ∅ := by
    ext stage
    exact isEmptyElim stage
  rw [liftedErrors, herrors, Finset.image_empty, Finset.union_empty]
  exact hmatch

theorem freshRisk_stop_empty {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (next : ℕ) [IsEmpty (I.freshSuffix next).Stage]
    (old : Finset I.Stage) (hmatch : Matchable I old) (ν : Measure Seed) :
    freshRisk input next old
      (stopPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
        (zeroNormalAccounting (I.freshSuffix next)) Seed).rule ν = 0 := by
  have hset : {sample | ¬ freshSuccess input next old
      (stopPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
        (zeroNormalAccounting (I.freshSuffix next)) Seed).rule sample} = ∅ := by
    ext sample
    change (¬ freshSuccess input next old
      (stopPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
        (zeroNormalAccounting (I.freshSuffix next)) Seed).rule sample) ↔ False
    constructor
    · intro hfail
      exact hfail (freshSuccess_stop_empty input next old hmatch sample)
    · exact False.elim
  simp only [freshRisk, hset, measure_empty]

/-- Second ORIGINAL R04 boundary, using the existing real stop Policy and
preserving original old H even when next is strictly past the last stage. -/
theorem freshPenalty_past_end (input : StatisticalInput I) (next : ℕ) (hnext : I.stageCount ≤ next)
    (old : Finset I.Stage) (hmatch : Matchable I old) (penalty : ℝ≥0∞) :
    freshPenalty input next old penalty = 0 := by
  let : IsEmpty (I.freshSuffix next).Stage := I.freshSuffix_isEmpty_stage next hnext
  let ν : Measure Unit := Measure.dirac ()
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have h := freshPenalty_le_policy input next old penalty ν
    (stopPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)) Unit)
  rw [freshObjective, stop_expectedObservationBill, freshRisk_stop_empty input next old hmatch ν,
    mul_zero, add_zero] at h
  exact le_antisymm h zero_le

end PaperProofs.Retained.PRetFreshTerminalBoundary040
