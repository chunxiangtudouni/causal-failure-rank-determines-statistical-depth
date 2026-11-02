module

public import PaperProofs.Paid.BridgeClaims
public import PaperProofs.Paid.CalibratedBackend

/-!
Exact first-round D29/D32/D36 interfaces of the frozen paid-extension and
bridge. The native paid witness is the FIXED calibratedAlgorithmPolicy;
the free witness is the FIXED original referenceBoundedPolicy, with budget
delta and precisely its original quotaExponent. No arbitrary controller
family, price/value oracle or optimized I=I_pay equality is introduced.

The numerical Q_joint/H certificate has no fee argument. Normal-call
qualification is pointwise for the actual fee's fixed script. It is not
inferred from arithmetic or required uniformly over all hypothetical fees.
The small-risk cutoff precedes ALL fee/cap/accounting choices, so the price
conclusion covers every nonnegative rational function f(delta) uniformly.
Concrete I/O bounds for arbitrary accounting remain the original M08 gap.

All performance/asymptotic statements remain unproved Prop definitions.
Only the arithmetic implication from joint resources plus the two genuine
normal-call certificates to the two original qualifications is proved.
Delta remains the original rational model input; no real-delta transport,
smaller risk target, enlarged quota or restriction of a comparator is used.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Paid

open Common Common.Native Statistics

namespace Parameters

/-- D29: the original full native separation, with its fixed algorithmic
sandwich. The lower statement is cap-independent; the upper witness uses
only the original THIS-script qualification. All bills include failures. -/
def NativeSeparationClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance),
    P.separationScale C .native accounting fee / 129 ≤ P.nativeValue C accounting fee hfee ∧
    (P.CalibratedOriginalQualification fee hfee C accounting →
      P.nativeValue C accounting fee hfee ≤ 72 * P.separationScale C .native accounting fee ∧
      ∃ policy : Policy (P.input fee hfee) C.val .native accounting P.CalibratedSearchSeed,
        policy.rule = P.calibratedAlgorithmRule fee ∧
        (∀ sample n, run (P.input fee hfee) C.val .native accounting policy.rule sample n =
          run (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) sample n) ∧
        risk (P.input fee hfee) C.val .native accounting policy.rule (P.calibratedAlgorithmSeedLaw fee) ≤ P.targetRisk ∧
        P.uncappedValue C accounting fee hfee ≤ P.nativeValue C accounting fee hfee ∧
        P.nativeValue C accounting fee hfee ≤
          expectedBill (P.input fee hfee) C.val .native accounting policy.rule (P.calibratedAlgorithmSeedLaw fee) ∧
        expectedBill (P.input fee hfee) C.val .native accounting policy.rule (P.calibratedAlgorithmSeedLaw fee) ≤
          8 * P.uncappedValue C accounting fee hfee)

end Parameters

namespace FixedSharedPool

/-- The common BSC specialization of the ORIGINAL structural certificate,
and the ORIGINAL fee-independent paid certificate, at EXACTLY delta. -/
def jointQuota (pool : FixedSharedPool) (delta : ℚ) (hd : 0 < delta) (hs : delta ≤ 1 / 64) : ℕ :=
  max (pool.freeQuota delta) (pool.atRisk delta hd hs).certificate.Q

/-- Exactly the arithmetic part of eq:joint-certificate. It deliberately
contains neither a fee argument nor a controller/performance assertion. -/
structure JointNumericalQualification (pool : FixedSharedPool) (delta : ℚ)
    (hd : 0 < delta) (hs : delta ≤ 1 / 64) (C : Contract pool.sharedInstance) : Prop where
  stage_quota : ∀ stage, pool.jointQuota delta hd hs ≤ C.reviewQuota stage
  total_calls : C.normalCallBound + pool.stages * pool.jointQuota delta hd hs + pool.tools ≤ C.totalCallCap

/-- The actual original free script, using delta as its executable budget
and the exponent already defining freeQuota. It executes repairs now. -/
def jointFreePolicy (pool : FixedSharedPool) (delta : ℚ)
    (C : Contract pool.sharedInstance) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting pool.sharedInstance) :
    Policy (pool.input 0 (by norm_num)) C .uncapped accounting Unit :=
  referenceBoundedPolicy (pool.input 0 (by norm_num)) C hC.1.1 accounting pool.sharedInstance.tools
    delta (BinaryExperiment.quotaExponent delta pool.stages)

/-- The ORIGINAL joint operation qualification: the same C/H0/accounting
for the two FIXED scripts. The paid field concerns this actual fee only.
No existence of a family or risk/cost/ET statement is a qualification field. -/
structure JointControllerQualification (pool : FixedSharedPool) (delta : ℚ)
    (hd : 0 < delta) (hs : delta ≤ 1 / 64) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract pool.sharedInstance) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting pool.sharedInstance) : Prop where
  resources : pool.JointNumericalQualification delta hd hs C
  free_normal : NormalCallCertificate (pool.input 0 (by norm_num)) C .uncapped accounting
    (pool.jointFreePolicy delta C hC accounting) C.normalCallBound
  paid_normal : NormalCallCertificate ((pool.atRisk delta hd hs).input fee hfee) C .uncapped accounting
    ((pool.atRisk delta hd hs).calibratedAlgorithmPolicy fee hfee ⟨C, hC⟩ accounting) C.normalCallBound

theorem jointQuota_ge_free (pool : FixedSharedPool) (delta : ℚ) (hd : 0 < delta) (hs : delta ≤ 1 / 64) :
    pool.freeQuota delta ≤ pool.jointQuota delta hd hs := le_max_left _ _

theorem jointQuota_ge_paid (pool : FixedSharedPool) (delta : ℚ) (hd : 0 < delta) (hs : delta ≤ 1 / 64) :
    (pool.atRisk delta hd hs).certificate.Q ≤ pool.jointQuota delta hd hs := le_max_right _ _

theorem jointFreeQuota_eq (pool : FixedSharedPool) (delta : ℚ) (stage : pool.sharedInstance.Stage) :
    referenceQuota (pool.input 0 (by norm_num)) (BinaryExperiment.quotaExponent delta pool.stages) stage =
      pool.freeQuota delta := rfl

/-- Rational delta itself is the original free risk choice. No substitute
budget is selected, and its exponent is exactly the one in freeQuota. -/
theorem jointFreeRiskChoice (pool : FixedSharedPool) (delta : ℚ)
    (hd : 0 < delta) (hs : delta ≤ 1 / 64) :
    ReferenceRiskChoice pool.stages (delta : ℝ)
      (BinaryExperiment.quotaExponent delta pool.stages) delta := by
  refine ⟨hd, by linarith, ?_, le_rfl, BinaryExperiment.quotaExponent_minimal delta hd pool.stages, rfl⟩
  have hpositive : (0 : ℝ) < delta := by exact_mod_cast hd
  linarith

theorem jointFreeQuota_sum (pool : FixedSharedPool) (delta : ℚ) :
    (∑ stage : pool.sharedInstance.Stage,
      referenceQuota (pool.input 0 (by norm_num)) (BinaryExperiment.quotaExponent delta pool.stages) stage) =
        pool.stages * pool.freeQuota delta := by
  have hcard : Fintype.card pool.sharedInstance.Stage = pool.stages := by
    simp only [sharedInstance, freshInstance, Instance.Stage, List.length_replicate, Fintype.card_fin]
  simp only [jointFreeQuota_eq, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, hcard]

/-- The free script's original normal-call input is retained, while its
quota/H arithmetic is genuinely derived from max(Q_comp,Q_pay). -/
theorem jointQualification_free (pool : FixedSharedPool) (delta : ℚ)
    (hd : 0 < delta) (hs : delta ≤ 1 / 64) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract pool.sharedInstance) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting pool.sharedInstance)
    (qualification : pool.JointControllerQualification delta hd hs fee hfee C hC accounting) :
    pool.FreeControllerQualification delta C hC accounting := by
  refine ⟨?_, ?_, qualification.free_normal⟩
  · intro stage
    exact (pool.jointQuota_ge_free delta hd hs).trans (qualification.resources.stage_quota stage)
  · rw [pool.jointFreeQuota_sum delta]
    have hstage : pool.sharedInstance.stageCount = pool.stages := by
      simp only [sharedInstance, freshInstance, Instance.stageCount, List.length_replicate]
    have htools : pool.sharedInstance.toolCount = pool.tools := rfl
    rw [hstage, htools, Nat.min_eq_right pool.tools_lt_stages.le]
    have hproduct := Nat.mul_le_mul_left pool.stages (pool.jointQuota_ge_free delta hd hs)
    have htotal := qualification.resources.total_calls
    omega

theorem jointQualification_paid (pool : FixedSharedPool) (delta : ℚ)
    (hd : 0 < delta) (hs : delta ≤ 1 / 64) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract pool.sharedInstance) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting pool.sharedInstance)
    (qualification : pool.JointControllerQualification delta hd hs fee hfee C hC accounting) :
    (pool.atRisk delta hd hs).CalibratedOriginalQualification fee hfee ⟨C, hC⟩ accounting := by
  refine ⟨⟨?_, ?_⟩, qualification.paid_normal⟩
  · intro stage
    exact (pool.jointQuota_ge_paid delta hd hs).trans (qualification.resources.stage_quota stage)
  · have hproduct := Nat.mul_le_mul_left pool.stages (pool.jointQuota_ge_paid delta hd hs)
    have htotal := qualification.resources.total_calls
    exact le_trans (Nat.add_le_add_right (Nat.add_le_add_left hproduct C.normalCallBound) pool.tools) htotal

/-- D32's implication uses the actual scripts; the numerical certificate
does not imply either normal-call field by itself. No converse is asserted. -/
def JointCertificateClaims (pool : FixedSharedPool) : Prop :=
  ∀ (delta : ℚ) (hd : 0 < delta) (hs : delta ≤ 1 / 64) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract pool.sharedInstance) (hC : C.IsCurrentPayment) (accounting : NormalAccounting pool.sharedInstance),
    pool.JointControllerQualification delta hd hs fee hfee C hC accounting →
      pool.FreeControllerQualification delta C hC accounting ∧
        (pool.atRisk delta hd hs).CalibratedOriginalQualification fee hfee ⟨C, hC⟩ accounting

theorem jointCertificateClaims (pool : FixedSharedPool) : pool.JointCertificateClaims := by
  intro delta hd hs fee hfee C hC accounting qualification
  exact ⟨pool.jointQualification_free delta hd hs fee hfee C hC accounting qualification,
    pool.jointQualification_paid delta hd hs fee hfee C hC accounting qualification⟩

theorem atRisk_nativeValue (pool : FixedSharedPool) (delta : ℚ) (hd : 0 < delta) (hs : delta ≤ 1 / 64)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract pool.sharedInstance) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting pool.sharedInstance) :
    (pool.atRisk delta hd hs).nativeValue ⟨C, hC⟩ accounting fee hfee =
      pool.nativeValue delta fee hfee C accounting := rfl

/-- D36: one epsilon-cutoff after fixing N,K,c,gamma, BEFORE choosing any
original rational delta, nonnegative fee, qualified caps or accounting.
Thus arbitrary rational f(delta) is covered with the SAME cutoff. Neither
the original Native.value comparator nor its risk target is changed. -/
def FixedPoolUniformFeePrice (pool : FixedSharedPool) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 → ∃ cutoff : ℝ, 0 < cutoff ∧
    ∀ (delta : ℚ) (hd : 0 < delta) (hs : delta ≤ 1 / 64), (delta : ℝ) < cutoff →
      ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract pool.sharedInstance)
        (hC : C.IsCurrentPayment) (accounting : NormalAccounting pool.sharedInstance),
        pool.JointControllerQualification delta hd hs fee hfee C hC accounting →
          pool.FixedPoolPriceNumericalConclusion delta fee hfee C accounting epsilon

/-- The stated K=0 asymptotic B_delta~S_delta is separate from the already
proved exact fee-independence of the entire input and Native.value. -/
def ZeroToolsStructuralSaturation (pool : FixedSharedPool) : Prop :=
  pool.tools = 0 →
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 → ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ delta : ℚ, 0 < delta → delta ≤ 1 / 64 → (delta : ℝ) < cutoff →
        ENNReal.ofReal ((1 - epsilon) * pool.structuralScaleReal delta) ≤ pool.saturationScale delta ∧
          pool.saturationScale delta ≤ ENNReal.ofReal ((1 + epsilon) * pool.structuralScaleReal delta)

def FixedPoolNativePriceClaims (pool : FixedSharedPool) : Prop :=
  pool.FixedPoolUniformFeePrice ∧ pool.ZeroToolsFeeIndependence ∧ pool.ZeroToolsStructuralSaturation

end FixedSharedPool
end PaperProofs.Paid
