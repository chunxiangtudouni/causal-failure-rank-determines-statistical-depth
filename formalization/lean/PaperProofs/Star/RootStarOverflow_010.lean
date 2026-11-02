module

public import PaperProofs.Star.RootStarOverflow_008
public import PaperProofs.Star.RootStarOverflow_002
public import PaperProofs.Common.NativeCapTransfer

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

/-- The only pending inputs are the original overflow assembly and the actual
ideal-script risk guarantee. The original qualification alone supplies native
resources; it never assumes a risk, price or finite-cost conclusion. -/
theorem nativeStarImplementation_of_risk (P : Parameters) (hoverflow : P.StarOverflowAssembly)
    (hrisk : ∀ (order : Order) (kind : PortKind) (C : Contract (starInstance P.tools order)), kind.contracts C →
      ∀ (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ), 0 < r → r ≤ 1 / 4 →
        risk (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none (Seed := Unit))
          (Measure.dirac ()) ≤ ENNReal.ofReal r) : P.NativeStarImplementation := by
  intro order kind C hC accounting delta exponent hd hq qualification
  let rule := P.starReferenceRule order kind (delta / 2) (some (P.commonQuota exponent)) (Seed := Unit)
  let bounded : Policy (P.input order) C .uncapped accounting Unit :=
    ⟨rule, P.measurable_starReferenceRule order kind (delta / 2) (some (P.commonQuota exponent)),
      star_legal_uncapped P order kind (delta / 2) (some (P.commonQuota exponent)) C hC accounting⟩
  let quota := fun _stage : (starInstance P.tools order).Stage => P.commonQuota exponent
  have hreviews : ReviewQuotaCertificate (P.input order) C accounting bounded.rule quota :=
    reviewQuotaCertificate P order kind (delta / 2) (P.commonQuota exponent) C hC accounting
  have hnormal : NormalCallCertificate (P.input order) C .uncapped accounting bounded C.normalCallBound :=
    qualification.normal_calls
  have hcard : (Finset.univ : Finset (starInstance P.tools order).Stage).card = P.tools + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
    simp only [starInstance, List.length_ofFn]
  have hmin : min (starInstance P.tools order).stageCount (starInstance P.tools order).toolCount = P.tools := by
    rw [stageCount_eq]
    change min (P.tools + 1) P.tools = P.tools
    omega
  have htotal : C.normalCallBound + ∑ stage, quota stage +
      min (starInstance P.tools order).stageCount (starInstance P.tools order).toolCount ≤ C.totalCallCap := by
    simpa [quota, hcard, nsmul_eq_mul, hmin] using qualification.total_calls
  let native := bounded.enforceCaps (P.input order) C accounting quota hreviews hnormal qualification.stage_quota htotal
  refine ⟨native, rfl, ?_, ?_⟩
  · rw [enforceCaps_risk_eq]
    have hassembly := hoverflow order kind C hC accounting delta exponent hd hq qualification.minimal_exponent
    have hideal := hrisk order kind C hC accounting (delta / 2) (by linarith) (by linarith)
    calc
      _ ≤ risk (P.input order) C .uncapped accounting
          (P.starReferenceRule order kind (delta / 2) none (Seed := Unit)) (Measure.dirac ()) +
            (P.input order).seededWorldLaw (Measure.dirac ())
              (P.anyStarOverflow order kind (delta / 2) (P.commonQuota exponent) C accounting) := hassembly.2.2.2
      _ ≤ ENNReal.ofReal (delta / 2) + ENNReal.ofReal (delta / 2) := add_le_add hideal hassembly.2.2.1
      _ = ENNReal.ofReal delta := by
        rw [← ENNReal.ofReal_add (by linarith : 0 ≤ delta / 2) (by linarith : 0 ≤ delta / 2)]
        congr 1
        ring
  · rw [enforceCaps_expectedBill_eq]
    apply lintegral_mono
    intro sample
    exact (sameTapeStarTruncation P order kind C hC accounting (delta / 2) (P.commonQuota exponent)
      (by linarith) (by linarith) sample).2

end RootStarOverflow
