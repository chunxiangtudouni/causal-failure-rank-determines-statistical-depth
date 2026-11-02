module

public import PaperProofs.Paid.PDLower_RankCoefficient_003
public import PaperProofs.Common.HealthyPriceClosure
public import PaperProofs.Paid.NativeJointClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Structure
open PaperProofs.Statistics PaperProofs.Paid

namespace PDLower

theorem fixedPool_rank (pool : FixedSharedPool) :
    errorRank pool.sharedInstance.compatibility pool.sharedInstance.tools =
      ((pool.tools + 1 : ℕ) : ℕ∞) := by
  exact paid_shared_rank (pool.atRisk (1 / 64) (by norm_num) (by norm_num))

theorem fixedPool_coefficient (pool : FixedSharedPool) :
    (pool.input 0 (by norm_num)).orderedCoefficient pool.sharedInstance.tools =
      pool.channel.a * (pool.stages - pool.tools : ℕ) := by
  exact paid_shared_coefficient (pool.atRisk (1 / 64) (by norm_num) (by norm_num)) 0 (by norm_num)

theorem freeNativeSqueeze (pool : FixedSharedPool) : pool.FreeNativeSqueeze := by
  intro epsilon hepsilon _hepsilonOne
  obtain ⟨lowerCutoff, hlowerCutoff, hlower⟩ :=
    (pool.input 0 (by norm_num)).nativeLowerPriceLaw (pool.tools + 1) (fixedPool_rank pool)
      epsilon hepsilon
  obtain ⟨upperCutoff, hupperCutoff, hupper⟩ :=
    (pool.input 0 (by norm_num)).nativeUpperPriceLaw (pool.tools + 1) (fixedPool_rank pool)
      epsilon hepsilon
  refine ⟨min lowerCutoff upperCutoff, lt_min hlowerCutoff hupperCutoff, ?_⟩
  intro delta hdelta hsmall hcutoff C hC accounting qualification
  have hdeltaReal : (0 : ℝ) < delta := by exact_mod_cast hdelta
  have hsmallReal : (delta : ℝ) ≤ 1 / 2 := by
    have hsmallCast := (Rat.cast_le (K := ℝ)).mpr hsmall
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hsmallCast
    linarith
  have hstageCount : pool.sharedInstance.stageCount = pool.stages := by
    simp only [FixedSharedPool.sharedInstance, freshInstance, Instance.stageCount,
      List.length_replicate]
  have choice : ReferenceRiskChoice pool.sharedInstance.stageCount (delta : ℝ)
      (BinaryExperiment.quotaExponent delta pool.stages) delta := by
    simpa only [hstageCount] using pool.jointFreeRiskChoice delta hdelta hsmall
  constructor
  · have lower := hlower (delta : ℝ) hdeltaReal
      (hcutoff.trans_le (min_le_left _ _)) C hC.1 accounting
    rw [fixedPool_coefficient] at lower
    simpa only [FixedSharedPool.nativeValue, FixedSharedPool.structuralScaleReal, mul_assoc]
      using lower
  · have upper := hupper (delta : ℝ) (BinaryExperiment.quotaExponent delta pool.stages) delta
      hdeltaReal (hcutoff.trans_le (min_le_right _ _)) hsmallReal choice C hC.1 accounting qualification
    rw [fixedPool_coefficient] at upper
    simpa only [FixedSharedPool.nativeValue, FixedSharedPool.structuralScaleReal, mul_assoc]
      using upper

end PDLower
