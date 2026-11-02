module

public import PaperProofs.Star.PreReportFailure
public import PaperProofs.Star.NativeInformation

/-!
The C05 Jensen lower step is proved directly in ENNReal. A supporting
logarithm inequality is integrated only AFTER adding the nonnegative q/delta
term. No logarithmic Bochner integrability, RCP, success conditioning, or
finite-cost assumption is introduced. Infinite integrals remain infinite.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Statistics.BinarySymmetric

theorem log_inv_support (q delta : ℝ) (hq : 0 < q) (hdelta : 0 < delta) :
    Real.log delta⁻¹ + 1 - q / delta ≤ Real.log q⁻¹ := by
  have h := Real.log_le_sub_one_of_pos (div_pos hq hdelta)
  rw [Real.log_div hq.ne' hdelta.ne'] at h
  simp only [Real.log_inv]
  linarith

theorem phi_sum_support {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hhalf : ∀ i, p i ≤ 1 / 2) (delta : ℝ) (hdelta : 0 < delta) :
    ENNReal.ofReal (Real.log delta⁻¹ + 1 - 2 * Fintype.card ι) ≤
      (∑ i, phi (p i)) + ENNReal.ofReal delta⁻¹ * ∏ i, ENNReal.ofReal (p i) := by
  classical
  have hprod : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => hp i)
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => log_inv_sub_two_le_phiReal (hp i) (hhalf i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hlogs : Real.log (∏ i, p i)⁻¹ = ∑ i, Real.log (1 / p i) := by
    rw [Real.log_inv, Real.log_prod (fun i _ => (hp i).ne')]
    simp only [one_div, Real.log_inv, Finset.sum_neg_distrib]
  have hsupport := log_inv_support (∏ i, p i) delta hprod hdelta
  rw [hlogs] at hsupport
  have hscalar : Real.log delta⁻¹ + 1 - 2 * Fintype.card ι ≤
      (∑ i, phiReal (p i)) + (∏ i, p i) / delta := by linarith
  calc
    _ ≤ ENNReal.ofReal ((∑ i, phiReal (p i)) + (∏ i, p i) / delta) := ENNReal.ofReal_le_ofReal hscalar
    _ = _ := by
      rw [ENNReal.ofReal_add
        (Finset.sum_nonneg (fun i _ => phiReal_nonneg (hp i) (hhalf i)))
        (div_nonneg hprod.le hdelta.le),
        ENNReal.ofReal_sum_of_nonneg (fun i _ => phiReal_nonneg (hp i) (hhalf i))]
      simp_rw [phi_of_pos (hp _)]
      congr 1
      rw [div_eq_mul_inv, ENNReal.ofReal_mul hprod.le,
        ENNReal.ofReal_prod_of_nonneg (fun i _ => (hp i).le), mul_comm]

/-- Probability-space Jensen step for finite positive posterior errors.
Only the product must be measurable. There is no integrability hypothesis,
even for the information integrand, and no conversion through toReal. -/
theorem phi_sum_lintegral_lower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ι → Ω → ℝ)
    (hp : ∀ ω i, 0 < p i ω) (hhalf : ∀ ω i, p i ω ≤ 1 / 2)
    (hmeas : Measurable (fun ω => ∏ i, ENNReal.ofReal (p i ω)))
    (delta : ℝ) (hdelta : 0 < delta)
    (hproduct : (∫⁻ ω, ∏ i, ENNReal.ofReal (p i ω) ∂μ) ≤ ENNReal.ofReal delta) :
    ENNReal.ofReal (Real.log delta⁻¹ - 2 * Fintype.card ι) ≤ ∫⁻ ω, ∑ i, phi (p i ω) ∂μ := by
  classical
  let information := fun ω => ∑ i, phi (p i ω)
  let scaledProduct := fun ω => ENNReal.ofReal delta⁻¹ * ∏ i, ENNReal.ofReal (p i ω)
  have hscaledMeas : Measurable scaledProduct := measurable_const.mul hmeas
  have hscaled : (∫⁻ ω, scaledProduct ω ∂μ) ≤ 1 := by
    rw [show scaledProduct = (fun ω => ENNReal.ofReal delta⁻¹ * ∏ i, ENNReal.ofReal (p i ω)) from rfl,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc
      _ ≤ ENNReal.ofReal delta⁻¹ * ENNReal.ofReal delta := mul_le_mul_right hproduct _
      _ = 1 := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hdelta.le), inv_mul_cancel₀ hdelta.ne', ENNReal.ofReal_one]
  have hpoint : ∀ ω, ENNReal.ofReal (Real.log delta⁻¹ + 1 - 2 * Fintype.card ι) ≤
      information ω + scaledProduct ω := fun ω => phi_sum_support (fun i => p i ω) (hp ω) (hhalf ω) delta hdelta
  have hintegral : ENNReal.ofReal (Real.log delta⁻¹ + 1 - 2 * Fintype.card ι) ≤
      (∫⁻ ω, information ω ∂μ) + 1 := by
    calc
      _ = ∫⁻ _ω : Ω, ENNReal.ofReal (Real.log delta⁻¹ + 1 - 2 * Fintype.card ι) ∂μ := by simp
      _ ≤ ∫⁻ ω, information ω + scaledProduct ω ∂μ := lintegral_mono hpoint
      _ = (∫⁻ ω, information ω ∂μ) + ∫⁻ ω, scaledProduct ω ∂μ := lintegral_add_right information hscaledMeas
      _ ≤ _ := add_le_add_right hscaled _
  by_cases hnonneg : 0 ≤ Real.log delta⁻¹ - 2 * Fintype.card ι
  · have hrewrite : ENNReal.ofReal (Real.log delta⁻¹ + 1 - 2 * Fintype.card ι) =
        ENNReal.ofReal (Real.log delta⁻¹ - 2 * Fintype.card ι) + 1 := by
      rw [show Real.log delta⁻¹ + 1 - 2 * Fintype.card ι =
        (Real.log delta⁻¹ - 2 * Fintype.card ι) + 1 from by ring,
        ENNReal.ofReal_add hnonneg (by norm_num), ENNReal.ofReal_one]
    rw [hrewrite] at hintegral
    exact (ENNReal.add_le_add_iff_right (by simp)).mp hintegral
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hnonneg)]
    exact zero_le

end PaperProofs.Statistics.BinarySymmetric

namespace PaperProofs.Star.Parameters

open Common Common.Native Statistics.BinarySymmetric

universe u

/-- Full native C05 lower conclusion from the two separately stated true
native interfaces. Their proofs are not reclassified as policy assumptions. -/
theorem nativeLateObservationLower_of_bridges (P : Star.Parameters)
    (hinformation : P.NativeLateObservationInformation.{u})
    (hfailure : P.PreReportFailureLower.{u}) : P.NativeLateObservationLower.{u} := by
  intro order C hlate accounting Seed m ν hν policy delta hdelta hsafe
  let μ := preReportLaw (P.input order) C accounting policy.rule ν
  let : IsProbabilityMeasure μ := by dsimp [μ, preReportLaw]; infer_instance
  have hprodMeas : Measurable
      (fun record : Seed × List (VisibleEvent (starInstance P.tools order)) =>
        ∏ i, ENNReal.ofReal (P.preReportMAPError order record.2 i)) :=
    (measurable_of_countable (fun history => ∏ i, ENNReal.ofReal (P.preReportMAPError order history i))).comp measurable_snd
  have hproduct :
      (∫⁻ record, ∏ i, ENNReal.ofReal (P.preReportMAPError order record.2 i) ∂μ) ≤ ENNReal.ofReal delta := by
    have hbound := hfailure order C hlate accounting Seed m ν hν policy Set.univ MeasurableSet.univ
    have hrisk : (∫⁻ record, ∏ i, ENNReal.ofReal (P.preReportMAPError order record.2 i) ∂μ) ≤
        risk (P.input order) C .native accounting policy.rule ν := by
      simpa only [Set.indicator_univ, Set.mem_univ, true_and, risk, μ] using hbound
    exact hrisk.trans hsafe
  have hlower := phi_sum_lintegral_lower μ
    (fun i record => P.preReportMAPError order record.2 i)
    (fun record i => P.preReportMAPError_pos order record.2 i)
    (fun record i => P.preReportMAPError_le_half order record.2 i)
    hprodMeas delta hdelta hproduct
  have hcard : Fintype.card (starInstance P.tools order).Stage = P.tools + 1 := by
    simp only [Instance.Stage, Fintype.card_fin]
    exact stageCount_eq P.tools order
  rw [hcard] at hlower
  calc
    _ = ENNReal.ofReal P.channel.a * ENNReal.ofReal (Real.log delta⁻¹ - 2 * (P.tools + 1 : ℕ)) := by
      rw [← ENNReal.ofReal_mul P.channel.a_pos.le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal P.channel.a *
        ∫⁻ record, ∑ i, phi (P.preReportMAPError order record.2 i) ∂μ := mul_le_mul_right hlower _
    _ = _ := (hinformation order C hlate accounting Seed m ν hν policy).symm

theorem nativeLateObservationLower_of_information (P : Star.Parameters)
    (hinformation : P.NativeLateObservationInformation.{u}) : P.NativeLateObservationLower.{u} :=
  P.nativeLateObservationLower_of_bridges hinformation P.preReportFailureLower

/-- The original complete native C05 lower statement, with both low-level
interfaces instantiated by their actual proved native theorems. -/
theorem nativeLateObservationLower (P : Star.Parameters) : P.NativeLateObservationLower.{u} :=
  P.nativeLateObservationLower_of_information P.nativeLateObservationInformation

theorem nativeLateLowerClaims (P : Star.Parameters) : P.NativeLateLowerClaims.{u} :=
  ⟨P.nativeLateObservationInformation, P.preReportFailureLower, P.nativeLateObservationLower⟩

end PaperProofs.Star.Parameters
