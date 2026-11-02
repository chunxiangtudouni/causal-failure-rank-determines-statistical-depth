module

public import PaperProofs.Retained.RootRetainedHead_002
public import PaperProofs.Retained.PRet_FullHistoryBridge_068
public import PaperProofs.Common.NativeFreshness

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace RootRetainedHead

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained
open PaperProofs.Retained.PRetFullHistoryBridge068

variable {I : Instance}

theorem future_zero {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed) :
    runFutureObservationBill input C mode accounting policy 0 =
      runObservationBill input C mode accounting policy := by
  funext sample
  simp only [runFutureObservationBill, Nat.zero_le, Finset.filter_true,
    runObservationBill, Ledger.observationBill]

theorem initial_penalty_le_policy {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (hn : 0 < I.stageCount) (C : Contract I) (hC : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (mode : ResourceMode) (policy : Policy input C mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (penalty : ℝ≥0∞) :
    freshPenalty input 0 ∅ penalty ≤ expectedObservationBill input C mode accounting policy.rule ν +
      penalty * risk input C mode accounting policy.rule ν := by
  let stage : I.Stage := ⟨0, hn⟩
  have hgate : ∀ sample : Seed × input.World,
      input.preBirthView stage sample ∈ (Set.univ : Set (Seed × input.PastWorld stage)) →
        ∃ history, entryHistory input C mode accounting policy.rule stage sample = some history ∧
          reportedErrors I history stage.val = ∅ := by
    intro sample _
    exact ⟨[], entryHistory_stageZero input C mode accounting policy.rule stage rfl sample,
      by simp [reportedErrors, stage]⟩
  have h := fullHistoryPenaltyBridge input stage ∅ (healthy_initial I) C hC accounting mode Seed
    ‹MeasurableSpace Seed› ν ‹IsProbabilityMeasure ν› policy Set.univ MeasurableSet.univ hgate penalty
  simpa only [stage, Set.mem_univ, Set.ofPred_true, measure_univ, one_mul, Set.indicator_univ,
    true_and, future_zero, expectedObservationBill, risk] using h

theorem initial_inverse_lower (input : StatisticalInput I) (hn : 0 < I.stageCount)
    (C : Contract I) (hC : C.IsEarlyRetained) (accounting : NormalAccounting I) (δ : ℝ≥0∞) :
    freshPenalty input 0 ∅ δ⁻¹ - 1 ≤ value input C .native accounting δ := by
  unfold value
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  apply (show freshPenalty input 0 ∅ δ⁻¹ - 1 ≤
    expectedObservationBill input C .native accounting policy.val.rule ν from ?_).trans
      (expectedObservationBill_le_actual input C .native accounting policy.val.rule ν)
  apply tsub_le_iff_right.mpr
  exact (initial_penalty_le_policy input hn C hC accounting .native policy.val ν δ⁻¹).trans
    (add_le_add le_rfl ((mul_le_mul' le_rfl policy.property).trans (ENNReal.inv_mul_le_one δ)))

end RootRetainedHead
