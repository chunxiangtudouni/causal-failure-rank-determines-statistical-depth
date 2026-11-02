module
public import Structure.RootB23_Threshold_FactorSource_003
public import Common.PSTR_TM_ThresholdOddsFields_211

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.FinalSemantics
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Statistics

/-- This is the numerical value produced by the actual factor machine,
not a replacement factor supplied to the original input. -/
theorem factor_product_identity (risk : Rat) (depth : Nat) :
    (FactorSource.factorValue risk depth : Rat)*risk =
      risk/(2*controllerTarget risk depth) := by
  rw [PSTRTMThresholdDenominatorRaw202.target_denominator_identity]
  unfold FactorSource.factorValue PSTRTMThresholdBadFactor226.factor
  push_cast
  have nonzero : (controllerB risk depth : Rat)+1 ≠ 0 := by positivity
  field_simp [nonzero]
  ring

/-- The cap's actual value is exactly the original controller bad-risk
value. The identity even holds without strengthening the original
positive-risk / positive-depth qualification. -/
theorem badRisk_identity (risk : Rat) (depth : Nat) :
    min (1/4) ((FactorSource.factorValue risk depth : Rat)*risk) =
      controllerBadRisk risk (controllerTarget risk depth) := by
  rw [factor_product_identity]
  rfl

end RootB23.Threshold.FinalSemantics
