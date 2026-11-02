module

public import PaperProofs.Retained.RootRetainedInfinite_002
public import PaperProofs.Retained.PRet_InfiniteRisk_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace RootRetainedInfinite

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained

variable {I : Instance}

/-- The unchanged original native retained script has zero risk and zero
observations at infinite girth, with every actual correction still paid. -/
theorem nativeInfiniteGirthLaw (input : StatisticalInput I) : NativeInfiniteGirthLaw input := by
  intro top C hearly accounting budget exponent positive small qualification
  let policy := PRetNativeImplementation118.nativeBoundedPolicy input C hearly accounting budget exponent qualification
  have observations : expectedObservationBill input C .native accounting policy.rule (Measure.dirac ()) = 0 := by
    calc
      _ = expectedObservationBill input C .uncapped accounting
          (boundedPolicy input C hearly accounting budget exponent).rule (Measure.dirac ()) := by
        unfold expectedObservationBill
        apply lintegral_congr
        intro sample
        unfold runObservationBill
        apply iSup_congr
        intro n
        exact congrArg (fun state : State I => state.ledger.observationBill input.fees)
          (PRetNativeImplementation118.nativeBounded_run_eq input C hearly accounting budget exponent qualification sample n)
      _ = 0 := expectedObservationBill_zero input top C hearly accounting budget (some (referenceQuota input exponent))
  refine ⟨policy, rfl, ?_, observations, ?_⟩
  · rw [← risk_uncapped_eq_native input C accounting policy.rule policy.legal]
    change risk input C .uncapped accounting
      (retainedRule input budget (some (referenceQuota input exponent))) (Measure.dirac ()) = 0
    rw [rule_limit_eq input top budget (some (referenceQuota input exponent))]
    exact PRetInfiniteRisk.idealRisk_zero_of_girth_top input top C hearly accounting budget positive small
  · have full := expectedBill_le_observation_add input C .native accounting policy (Measure.dirac ())
    rw [observations, zero_add] at full
    exact full

end RootRetainedInfinite
