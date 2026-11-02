module

public import PaperProofs.Common.AvailableValue

/-! Empty tasks have value zero by a real stop policy, including infinite penalties. -/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

def stopPolicy (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (Seed : Type*) [MeasurableSpace Seed] :
    Policy input C mode accounting Seed where
  rule _ _ := .stop
  measurable_rule := measurable_const
  legal := by
    intro _ _ _ _ s _ hactive
    exact ⟨stopState s false, .stop s hactive⟩

theorem stop_run_one (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (sample : Seed × input.World) :
    run input C mode accounting (stopPolicy input C mode accounting Seed).rule sample 1 =
      stopState (initial (input.truthAt sample.2)) false := by
  exact run_succ_of_step input C mode accounting _ sample 0 _ rfl (.stop _ rfl)

theorem stop_runActualBill (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (sample : Seed × input.World) :
    runActualBill input C mode accounting (stopPolicy input C mode accounting Seed).rule sample = 0 := by
  have hh : (run input C mode accounting (stopPolicy input C mode accounting Seed).rule sample 1).halted =
      true := by rw [stop_run_one]; rfl
  rw [runActualBill_of_halted input C mode accounting _ sample 1 hh, stop_run_one,
    stop_actualBill, initial_actualBill]

theorem stop_expectedObservationBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (ν : Measure Seed) :
    expectedObservationBill input C mode accounting (stopPolicy input C mode accounting Seed).rule ν = 0 := by
  have heq (sample : Seed × input.World) :
      runObservationBill input C mode accounting (stopPolicy input C mode accounting Seed).rule sample = 0 :=
    le_antisymm ((runObservationBill_le_actual input C mode accounting _ sample).trans_eq
      (stop_runActualBill input C mode accounting sample)) zero_le
  simp only [expectedObservationBill, heq, lintegral_zero]

theorem stop_runSuccess_empty [IsEmpty I.Stage] (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (sample : Seed × input.World) :
    runSuccess input C mode accounting (stopPolicy input C mode accounting Seed).rule sample := by
  classical
  refine ⟨1, ?_, ?_⟩
  · rw [stop_run_one]; rfl
  · rw [stop_run_one]
    have hw : allWritten (initial (input.truthAt sample.2)).ledger := fun i => isEmptyElim i
    refine ⟨?_, rfl, ?_, ?_⟩
    · change decide (allWritten (initial (input.truthAt sample.2)).ledger) = true
      exact decide_eq_true hw
    · intro i; exact isEmptyElim i
    · intro i; exact isEmptyElim i

theorem stop_risk_empty [IsEmpty I.Stage] (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (ν : Measure Seed) :
    risk input C mode accounting (stopPolicy input C mode accounting Seed).rule ν = 0 := by
  have heq : {sample : Seed × input.World |
      ¬ runSuccess input C mode accounting (stopPolicy input C mode accounting Seed).rule sample} = ∅ := by
    ext sample
    simp only [Set.mem_ofPred_eq, stop_runSuccess_empty, not_true_eq_false, Set.mem_empty_iff_false]
  simp only [risk, heq, measure_empty]

theorem stopPolicy_usesOnly (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (Seed : Type*) [MeasurableSpace Seed] :
    UsesOnly input C accounting (stopPolicy input C .uncapped accounting Seed).rule available := by
  intro _ _ _ _ _ _ _ _ _ heq
  cases heq

theorem availablePenaltyValue_empty [IsEmpty I.Stage] (input : StatisticalInput I)
    (C : Contract I) (accounting : NormalAccounting I) (available : Finset I.Tool) (penalty : ℝ≥0∞) :
    availablePenaltyValue input C accounting available penalty = 0 := by
  let ν : Measure Unit := Measure.dirac ()
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have h := availablePenaltyValue_le_policy input C accounting available penalty ν
    ⟨stopPolicy input C .uncapped accounting Unit, stopPolicy_usesOnly input C accounting available Unit⟩
  change availablePenaltyValue input C accounting available penalty ≤
    penaltyObjective input C .uncapped accounting (stopPolicy input C .uncapped accounting Unit).rule ν penalty at h
  rw [penaltyObjective, stop_expectedObservationBill, stop_risk_empty, mul_zero, add_zero] at h
  exact le_antisymm h zero_le

end PaperProofs.Common.Native
