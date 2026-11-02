module

public import PaperProofs.Paid.PDLower_BlindAdversary_001
public import PaperProofs.Paid.PDLower_BlindTruthLaw_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

universe u

theorem zero_quota_risk_lower (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (hquota : ∀ stage, C.reviewQuota stage = 0) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : Policy (P.input fee hf) C .native accounting Seed) :
    ENNReal.ofReal (((1 / 2 : ℚ) ^ P.certificate.stages : ℚ) : ℝ) ≤
      risk (P.input fee hf) C .native accounting policy.rule ν := by
  let tapes : ReviewTapes (P.input fee hf) := fun _ _ => ⟨0, by change 0 < 2; decide⟩
  have hshort : P.sharedInstance.toolCount < P.sharedInstance.stageCount := by
    simpa only [Parameters.sharedInstance, Instance.stageCount, List.length_replicate]
      using P.tools_lt_stages
  have conditional (seed : Seed) :
      ENNReal.ofReal (((1 / 2 : ℚ) ^ P.certificate.stages : ℚ) : ℝ) ≤
        (P.input fee hf).worldLaw ((Prod.mk seed) ⁻¹'
          {sample | ¬ runSuccess (P.input fee hf) C .native accounting policy.rule sample}) := by
    obtain ⟨truth, failure⟩ := exists_failure_truth (P.input fee hf) C hearly hshort accounting
      policy.rule policy.legal seed tapes
    have subset : {world : (P.input fee hf).World | (P.input fee hf).truthAt world = truth} ⊆
        (Prod.mk seed) ⁻¹' {sample | ¬ runSuccess (P.input fee hf) C .native accounting policy.rule sample} := by
      intro world htruth success
      apply failure
      apply (zero_quota_success_truth_congr (P.input fee hf) C accounting hquota
        policy.rule policy.legal seed world (replayWorld (P.input fee hf) truth tapes) ?_).mp success
      exact htruth
    rw [← paid_truth_assignment_mass P fee hf truth]
    exact measure_mono subset
  calc
    _ = ∫⁻ _seed, ENNReal.ofReal (((1 / 2 : ℚ) ^ P.certificate.stages : ℚ) : ℝ) ∂ν := by simp
    _ ≤ ∫⁻ seed, (P.input fee hf).worldLaw ((Prod.mk seed) ⁻¹'
        {sample | ¬ runSuccess (P.input fee hf) C .native accounting policy.rule sample}) ∂ν :=
      lintegral_mono conditional
    _ = _ := (Measure.prod_apply (measurableSet_runSuccess (P.input fee hf) C .native accounting
      policy.rule policy.measurable_rule).compl).symm

theorem blindRiskMinimal (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee) (allocation : Deadline) :
    P.BlindRiskMinimal.{u} fee hf (P.retainedPaymentExampleContract allocation)
      (blindCallAccounting P.sharedInstance) := by
  intro Seed m
  let : MeasurableSpace Seed := m
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy
  simpa only [Rat.cast_pow] using
    zero_quota_risk_lower P fee hf (P.retainedPaymentExampleContract allocation) rfl
      (fun _ => rfl) (blindCallAccounting P.sharedInstance) ν policy

end PDLower
