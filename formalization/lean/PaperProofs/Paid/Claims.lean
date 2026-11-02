module

public import PaperProofs.Paid.Pricing
public import PaperProofs.Paid.BSCAdapter
public import PaperProofs.Statistics.BSCRoc

/-!
First-round statements from the frozen independent Appendix D.

Every policy/value below is the existing full visible-history native model,
with the SAME current-payment contract, accounting, original resource data,
input experiments and target risk. Charges are actual all-path charges in
ENNReal, including infinite expectations. Only the source theorem on paid
overlay assumes a finite-cost input policy. No MAP, finite-ET or feasibility
restriction is added to any comparison infimum.

D07, D12, D13, D15, D28 and D30 below are unproved propositions. D29 is
covered ONLY on its cap-independent lower side. The complete native upper
theorem and eight-factor algorithm still require an actual controller with
the original Q-review and H0 normal-call certificates. The numerical
NativeCapQualification alone is not that assumption: arbitrary accounting
can charge more than the entire H on one write. No native upper theorem is
asserted from that numerical condition here. D35 is proved separately as a
pure ENNReal perturbation inequality, including infinite baselines.
-/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Paid.Parameters

open Common
open Statistics.BinarySymmetric

universe u

/-- The original common target; in particular no risk splitting is hidden here. -/
noncomputable def targetRisk (P : PaperProofs.Paid.Parameters) : ℝ≥0∞ :=
  ENNReal.ofReal (P.certificate.risk : ℝ)

/-- D_f of paid-extension.tex:62--65, retaining the original c in a. -/
noncomputable def feeScaleReal (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℝ :=
  P.a * P.certificate.stages * Real.log (1 + (fee : ℝ) / P.a)

noncomputable def feeScale (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (P.feeScaleReal fee)

/-- S_delta of the same displayed formula, independent of f. -/
noncomputable def saturationScaleReal (P : PaperProofs.Paid.Parameters) : ℝ :=
  P.a * P.certificate.stages *
    Real.log (1 + (P.certificate.stages : ℝ) / (P.certificate.risk : ℝ))

noncomputable def saturationScale (P : PaperProofs.Paid.Parameters) : ℝ≥0∞ :=
  ENNReal.ofReal P.saturationScaleReal

theorem feeScaleReal_nonneg (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    0 ≤ P.feeScaleReal fee := by
  have hf : (0 : ℝ) ≤ fee := by exact_mod_cast hfee
  apply mul_nonneg (mul_nonneg P.a_pos.le (Nat.cast_nonneg _))
  exact Real.log_nonneg (by linarith [div_nonneg hf P.a_pos.le])

theorem saturationScaleReal_nonneg (P : PaperProofs.Paid.Parameters) :
    0 ≤ P.saturationScaleReal := by
  have hr : (0 : ℝ) < P.certificate.risk := by exact_mod_cast P.certificate.risk_pos
  apply mul_nonneg (mul_nonneg P.a_pos.le (Nat.cast_nonneg _))
  exact Real.log_nonneg (by linarith [div_nonneg (Nat.cast_nonneg P.certificate.stages) hr.le])

@[simp] theorem feeScale_zero (P : PaperProofs.Paid.Parameters) : P.feeScale 0 = 0 := by
  simp [feeScale, feeScaleReal]

theorem feeScale_ne_top (P : PaperProofs.Paid.Parameters) (fee : ℚ) : P.feeScale fee ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem saturationScale_ne_top (P : PaperProofs.Paid.Parameters) : P.saturationScale ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- T = min(A+D_f,S_delta), with exactly the original same-contract free A. -/
noncomputable def separationScale (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting P.sharedInstance)
    (fee : ℚ) : ℝ≥0∞ :=
  min (P.freeValue C mode accounting + P.feeScale fee) P.saturationScale

/-- D07's independent uniformly attainable surrogate, genuinely infinity at p=0. -/
noncomputable def rocSurrogate (P : PaperProofs.Paid.Parameters) (p : ℝ) : ℝ≥0∞ :=
  max (ENNReal.ofReal P.a * phi p)
    (ENNReal.ofReal ((P.reviewFee : ℝ) / (P.certificate.gamma : ℝ)) * ENNReal.ofReal (1 / 2 - p))

@[simp] theorem rocSurrogate_zero (P : PaperProofs.Paid.Parameters) : P.rocSurrogate 0 = ⊤ := by
  have ha : ENNReal.ofReal P.a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr P.a_pos)
  simp [rocSurrogate, phi_zero, ha]

/-- D07, lem:paid:surrogate and its adjacent-charge ratio (paid-proofs:173--194).
This is a target proposition, not a consequence assumed in the test model. -/
def UniformLocalSurrogate (P : PaperProofs.Paid.Parameters) : Prop :=
  (∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
    P.rocSurrogate p ≤ P.binarySymmetric.rocPrice p ∧
    P.binarySymmetric.rocPrice p ≤ 4 * P.rocSurrogate p) ∧
  ∀ m : ℕ, 1 ≤ m →
    P.binarySymmetric.endpointCharge (m + 1) ≤ 4 * P.binarySymmetric.endpointCharge m

/-- Exact D12 lower amount, including f=0 and arbitrarily small positive f. -/
noncomputable def feeScaleLowerAmount (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal ((P.a * P.certificate.stages / 128) *
    Real.log (1 + min ((fee : ℝ) / P.a)
      ((P.certificate.stages : ℝ) / (P.certificate.risk : ℝ))))

@[simp] theorem feeScaleLowerAmount_zero (P : PaperProofs.Paid.Parameters) :
    P.feeScaleLowerAmount 0 = 0 := by
  have hr : (0 : ℝ) < P.certificate.risk := by exact_mod_cast P.certificate.risk_pos
  have hratio : (0 : ℝ) ≤ (P.certificate.stages : ℝ) / (P.certificate.risk : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hr.le
  simp [feeScaleLowerAmount, min_eq_left hratio]

/-- D12, lem:paid:fee-scale. Every lawful randomized full-history policy is
included, in either mode. Infinite charges require no separate conversion. -/
def UniformFeeScalePolicyLower (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (fee : ℚ) (hfee : 0 ≤ fee) : Prop :=
  ∀ (mode : Native.ResourceMode) (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ p : Native.Policy (P.input fee hfee) C.val mode accounting Seed,
        Native.risk (P.input fee hfee) C.val mode accounting p.rule ν ≤ P.targetRisk →
        P.feeScaleLowerAmount fee ≤ Native.expectedBill (P.input fee hfee) C.val mode accounting p.rule ν

/-- The corresponding original full-policy infimum statement, in both modes. -/
def UniformFeeScaleValueLower (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (fee : ℚ) (hfee : 0 ≤ fee) : Prop :=
  ∀ mode, P.feeScaleLowerAmount fee ≤ P.paidValue C mode accounting fee hfee

/-- D13's p_f, with no logarithmic approximation near f=0. -/
noncomputable def overlayError (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℝ :=
  1 / (2 * (1 + (fee : ℝ) / P.a))

theorem overlayError_pos (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    0 < P.overlayError fee := by
  have hf : (0 : ℝ) ≤ fee := by exact_mod_cast hfee
  exact one_div_pos.mpr (mul_pos (by norm_num) (by linarith [div_nonneg hf P.a_pos.le]))

theorem overlayError_le_half (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    P.overlayError fee ≤ 1 / 2 := by
  have hf : (0 : ℝ) ≤ fee := by exact_mod_cast hfee
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
  linarith [div_nonneg hf P.a_pos.le]

@[simp] theorem overlayError_zero (P : PaperProofs.Paid.Parameters) : P.overlayError 0 = 1 / 2 := by
  simp [overlayError]

@[simp] theorem overlayError_zero_rocPrice (P : PaperProofs.Paid.Parameters) :
    P.binarySymmetric.rocPrice (P.overlayError 0) = 0 := by
  rw [overlayError_zero, P.binarySymmetric.rocPrice_half]

/-- D13, eq:paid:weighted-correction and eq:paid:overlay-local.
The actual fee term uses f, and the local charge remains ENNReal. -/
def OverlayLocalBounds (P : PaperProofs.Paid.Parameters) (fee : ℚ) : Prop :=
  (fee : ℝ) * P.overlayError fee ≤ P.a / 2 * Real.log (1 + (fee : ℝ) / P.a) ∧
  P.binarySymmetric.rocPrice (P.overlayError fee) ≤
    ENNReal.ofReal (8 * P.a * Real.log (1 + (fee : ℝ) / P.a))

/-- Exact original nonnegative-fee quantification for D13. -/
def OverlayLocalClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ fee : ℚ, 0 ≤ fee → P.OverlayLocalBounds fee

/-- The zero-price boundary is exact, rather than inferred from an
asymptotic approximation valid only for positive penalties. -/
theorem overlayLocalBounds_zero (P : PaperProofs.Paid.Parameters) : P.OverlayLocalBounds 0 := by
  constructor
  · simp [overlayError]
  · simpa only [Rat.cast_zero, zero_div, add_zero, Real.log_one, mul_zero, ENNReal.ofReal_zero]
      using le_of_eq P.overlayError_zero_rocPrice

/-- D15 policy statement: every finite-cost free policy, even one supplied
under native caps, admits a cap-relaxed paid simulator with no greater risk.
The output's small seed is sufficient by NativeSeed, not a finite-randomness
restriction. All input private-seed universes and non-MAP writes remain. -/
def PaidOverlayPolicy (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (fee : ℚ) (hfee : 0 ≤ fee) : Prop :=
  ∀ (mode : Native.ResourceMode) (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ p : Native.Policy (P.input 0 (by norm_num)) C.val mode accounting Seed,
        Native.expectedBill (P.input 0 (by norm_num)) C.val mode accounting p.rule ν ≠ ⊤ →
        ∃ (Seed' : Type) (m' : MeasurableSpace Seed'),
          letI : MeasurableSpace Seed' := m'
          ∃ (ν' : Measure Seed'), IsProbabilityMeasure ν' ∧
            ∃ paid : Native.Policy (P.input fee hfee) C.val .uncapped accounting Seed',
              Native.risk (P.input fee hfee) C.val .uncapped accounting paid.rule ν' ≤
                Native.risk (P.input 0 (by norm_num)) C.val mode accounting p.rule ν ∧
              Native.expectedBill (P.input fee hfee) C.val .uncapped accounting paid.rule ν' ≤
                Native.expectedObservationBill (P.input 0 (by norm_num)) C.val mode accounting p.rule ν +
                  (17 / 2 : ℝ≥0∞) * P.feeScale fee

/-- D15 value statement, not a claim that the overlay obeys native quotas. -/
def PaidOverlayValue (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (fee : ℚ) (hfee : 0 ≤ fee) : Prop :=
  P.uncappedValue C accounting fee hfee ≤ P.freeValue C .uncapped accounting + 9 * P.feeScale fee

/-- D28: a true uncapped policy makes no physical corrections on any path,
has the original target risk and pays all observations, also on failures.
No native Q-quota or H0 certificate is claimed for this majority witness. -/
def NoCorrectionPolicyComparison (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (fee : ℚ) (hfee : 0 ≤ fee) : Prop :=
  ∃ (Seed : Type) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∃ (ν : Measure Seed), IsProbabilityMeasure ν ∧
      ∃ p : Native.Policy (P.input fee hfee) C.val .uncapped accounting Seed,
        (∀ sample n,
          (Native.run (P.input fee hfee) C.val .uncapped accounting p.rule sample n).ledger.executions = []) ∧
        Native.risk (P.input fee hfee) C.val .uncapped accounting p.rule ν ≤ P.targetRisk ∧
        Native.expectedBill (P.input fee hfee) C.val .uncapped accounting p.rule ν ≤ 7 * P.saturationScale

def NoCorrectionValueComparison (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (fee : ℚ) (hfee : 0 ≤ fee) : Prop :=
  P.uncappedValue C accounting fee hfee ≤ 7 * P.saturationScale

/-- D29a ONLY: the native lower side needs no resource certificate.
D29's native upper side is intentionally not counted as stated here. -/
def NativeSeparationLower (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (fee : ℚ) (hfee : 0 ≤ fee) : Prop :=
  P.separationScale C .native accounting fee / 129 ≤ P.nativeValue C accounting fee hfee

/-- D30: the distinct, entirely uncapped two-sided comparison. The free
baseline is A_infinity with the same I_pay, never the larger I class. -/
def UncappedSeparation (P : PaperProofs.Paid.Parameters) (C : P.PaymentContract)
    (accounting : Native.NormalAccounting P.sharedInstance) (fee : ℚ) (hfee : 0 ≤ fee) : Prop :=
  P.separationScale C .uncapped accounting fee / 129 ≤ P.uncappedValue C accounting fee hfee ∧
  P.uncappedValue C accounting fee hfee ≤ 9 * P.separationScale C .uncapped accounting fee

/-- D35, bridge.tex:56--61. Independent of fees, caps and the particular
nonnegative scales; multiplication and minima also preserve infinity. -/
def MinPerturbation : Prop :=
  ∀ (ε : ℝ), 0 ≤ ε → ε < 1 → ∀ A B D S : ℝ≥0∞,
    ENNReal.ofReal (1 - ε) * B ≤ A → A ≤ ENNReal.ofReal (1 + ε) * B →
    ENNReal.ofReal (1 - ε) * min (B + D) S ≤ min (A + D) S ∧
    min (A + D) S ≤ ENNReal.ofReal (1 + ε) * min (B + D) S

theorem minPerturbation : MinPerturbation := by
  intro ε hε _hεone A B D S hlower hupper
  have hl : ENNReal.ofReal (1 - ε) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hu : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + ε) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  constructor
  · rw [mul_min, mul_add]
    exact min_le_min (add_le_add hlower (mul_le_of_le_one_left' hl)) (mul_le_of_le_one_left' hl)
  · rw [mul_min, mul_add]
    exact min_le_min (add_le_add hupper (le_mul_of_one_le_left' hu)) (le_mul_of_one_le_left' hu)

end PaperProofs.Paid.Parameters
