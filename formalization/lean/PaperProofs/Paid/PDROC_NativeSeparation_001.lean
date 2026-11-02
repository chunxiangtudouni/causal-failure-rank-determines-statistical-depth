module

public import PaperProofs.Paid.NativeJointClaims
public import PaperProofs.Paid.PDLower_Price_001
public import PaperProofs.Common.NativeSeed

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

/-- The original native comparator is a restriction of the original
uncapped comparator, without any fixed-script qualification. -/
theorem nativeSeparation_uncapped_le_native (P : Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee) :
    P.uncappedValue C accounting fee hf ≤ P.nativeValue C accounting fee hf :=
  P.uncappedValue_le_nativeValue C accounting fee hf

/-- D29 uses the native free baseline. Passing from the uncapped baseline
to that larger original baseline has this precise monotone direction. -/
theorem nativeSeparation_scale_uncapped_le_native (P : Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) :
    P.separationScale C .uncapped accounting fee ≤ P.separationScale C .native accounting fee := by
  apply min_le_min _ le_rfl
  exact add_le_add (P.uncappedValue_le_nativeValue C accounting 0 (by norm_num)) le_rfl

/-- The full original native lower bound, for every cap/contract/accounting;
this does not assume D26 or normal-call qualification. -/
theorem nativeSeparation_lower (P : Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee) :
    P.separationScale C .native accounting fee / 129 ≤ P.nativeValue C accounting fee hf :=
  PDLower.nativeSeparationLower P C accounting fee hf

universe u

/-- A real feasible native policy supplies its complete expected bill as
an upper bound on native value, for arbitrary private seed universe. -/
theorem nativeSeparation_native_le_feasibleBill (P : Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee)
    {Seed : Type u} [MeasurableSpace Seed]
    (policy : Policy (P.input fee hf) C.val .native accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hrisk : risk (P.input fee hf) C.val .native accounting policy.rule ν ≤ P.targetRisk) :
    P.nativeValue C accounting fee hf ≤ expectedBill (P.input fee hf) C.val .native accounting policy.rule ν :=
  value_le_policy_any_seed (P.input fee hf) C.val .native accounting policy ν P.targetRisk hrisk

/-- The original uncapped/native/fixed-policy-bill sandwich follows from
feasibility and the eight-factor full bill. Proving that bill for the
fixed calibrated backend is a separate remaining D26 obligation. -/
theorem nativeSeparation_feasible_sandwich (P : Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee)
    {Seed : Type u} [MeasurableSpace Seed]
    (policy : Policy (P.input fee hf) C.val .native accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hrisk : risk (P.input fee hf) C.val .native accounting policy.rule ν ≤ P.targetRisk)
    (hbill : expectedBill (P.input fee hf) C.val .native accounting policy.rule ν ≤
      8 * P.uncappedValue C accounting fee hf) :
    P.uncappedValue C accounting fee hf ≤ P.nativeValue C accounting fee hf ∧
      P.nativeValue C accounting fee hf ≤ expectedBill (P.input fee hf) C.val .native accounting policy.rule ν ∧
      expectedBill (P.input fee hf) C.val .native accounting policy.rule ν ≤ 8 * P.uncappedValue C accounting fee hf :=
  ⟨nativeSeparation_uncapped_le_native P C accounting fee hf,
    nativeSeparation_native_le_feasibleBill P C accounting fee hf policy ν hrisk, hbill⟩

/-- The factor72 comparison is a consequence of the original eight-factor
native backend bound and the original nine-factor uncapped bound. It does
not replace the fixed backend by an optimized policy family. -/
theorem nativeSeparation_upper_of_eight (P : Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee)
    (height : P.nativeValue C accounting fee hf ≤ 8 * P.uncappedValue C accounting fee hf)
    (huncapped : P.uncappedValue C accounting fee hf ≤ 9 * P.separationScale C .uncapped accounting fee) :
    P.nativeValue C accounting fee hf ≤ 72 * P.separationScale C .native accounting fee := by
  calc
    P.nativeValue C accounting fee hf ≤ 8 * P.uncappedValue C accounting fee hf := height
    _ ≤ 8 * (9 * P.separationScale C .uncapped accounting fee) := mul_le_mul' le_rfl huncapped
    _ ≤ 8 * (9 * P.separationScale C .native accounting fee) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (nativeSeparation_scale_uncapped_le_native P C accounting fee))
    _ = 72 * P.separationScale C .native accounting fee := by ring

end PDROC
