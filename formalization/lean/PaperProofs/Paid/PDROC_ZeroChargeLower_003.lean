module

public import PaperProofs.Paid.PDROC_ZeroChargeLower_002
public import PaperProofs.Paid.PDROC_ZeroChargeLower_Transport_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

namespace PDROC.ZeroChargeLower

universe u

/-- Exact original zero expected actual-bill lower field, for both original
resource modes and every private Seed universe. -/
theorem originalZeroChargePolicyLower (P : Parameters) :
    ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
      (accounting : NormalAccounting P.sharedInstance)
      (mode : ResourceMode) (Seed : Type u) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
        letI : IsProbabilityMeasure ν := hν
        ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
          expectedBill (P.input fee hfee) C.val mode accounting policy.rule ν = 0 →
            ENNReal.ofReal (P.zeroChargeRisk fee : ℝ) ≤
              risk (P.input fee hfee) C.val mode accounting policy.rule ν :=
  Transport.originalZeroChargePolicyLower_of_smallPenaltyValue P (smallPenaltyValue P)

/-- Exact original positive actual-cost floor. Infinite expected bills and
failed/nonreturn paths remain in the original all-path bill. -/
theorem originalPositiveCostFloor (P : Parameters) :
    ∀ (fee : ℚ) (hfee : 0 ≤ fee), P.certificate.risk < P.zeroChargeRisk fee →
      ∀ (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
        (mode : ResourceMode) (Seed : Type u) (m : MeasurableSpace Seed),
        letI : MeasurableSpace Seed := m
        ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
          letI : IsProbabilityMeasure ν := hν
          ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
            risk (P.input fee hfee) C.val mode accounting policy.rule ν ≤ P.targetRisk →
              ENNReal.ofReal (P.positiveValueFloor fee : ℝ) ≤
                expectedBill (P.input fee hfee) C.val mode accounting policy.rule ν :=
  Transport.originalPositiveCostFloor_of_smallPenaltyValue P (smallPenaltyValue P)

end PDROC.ZeroChargeLower
