module

public import PaperProofs.Star.PStar_ActualPrice_041

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarNativePrice042

open Common Common.Native Parameters MeasureTheory PStarActualPrice041
open scoped ENNReal

/-- The original native infimum is bounded by the actual qualified
implementation, against ALL randomized policies at the SAME delta. -/
theorem nativeValue_le_envelope_of_interfaces (P : PaperProofs.Star.Parameters)
    (universal : P.UniversalFirstCurrentConstruction) (count : P.CountControllerConstruction)
    (late : P.LateRetainedConstruction) (native : P.NativeStarImplementation)
    (order : Order) (kind : PortKind) (C : Contract (starInstance P.tools order))
    (qualified : kind.contracts C) (accounting : NormalAccounting (starInstance P.tools order))
    (delta : ℝ) (exponent : ℕ) (positive : 0 < delta) (small : delta ≤ 1/2)
    (qualification : P.OriginalStarQualification order kind delta exponent C accounting) :
    P.value order C .native accounting (ENNReal.ofReal delta) ≤
      ENNReal.ofReal (RootStarPriceEnvelope.observationEnvelope P order kind delta +
        (P.tools : ℝ)*(P.correctionFee : ℝ)) := by
  obtain ⟨policy, _sameRule, safe, dominated⟩ := native order kind C qualified accounting
    delta exponent positive small qualification
  exact (value_le_policy_any_seed (P.input order) C .native accounting policy
    (Measure.dirac ()) (ENNReal.ofReal delta) safe).trans
      (dominated.trans (idealActualBill_le_envelope P universal count late order kind C qualified
        accounting delta positive small))

/-- Original ThreePrices from its independent proven construction and
lower-law interfaces. One cutoff precedes both orders, three contracts,
all original caps, accountings and H0 qualifications. -/
theorem threePrices_of_interfaces (P : PaperProofs.Star.Parameters)
    (universal : P.UniversalFirstCurrentConstruction) (count : P.CountControllerConstruction)
    (late : P.LateRetainedConstruction) (native : P.NativeStarImplementation)
    (lowerLaw : P.ThreePricesLower) : P.ThreePrices := by
  intro epsilon positive lessOne
  obtain ⟨lowerCutoff, lowerPositive, lowerBound⟩ := lowerLaw epsilon positive lessOne
  obtain ⟨upperCutoff, upperPositive, upperBound⟩ := RootStarPriceEnvelope.uniform_upper P epsilon positive
  refine ⟨min lowerCutoff upperCutoff, lt_min lowerPositive upperPositive, ?_⟩
  intro delta deltaPositive cutoff small order kind
  have lowerCut : delta < lowerCutoff := lt_of_lt_of_le cutoff (min_le_left _ _)
  have upperCut : delta < upperCutoff := lt_of_lt_of_le cutoff (min_le_right _ _)
  obtain ⟨scalePositive, envelopeBound⟩ := upperBound delta deltaPositive upperCut small order kind
  refine ⟨scalePositive, ?_⟩
  intro C qualified accounting exponent qualification
  refine ⟨lowerBound delta deltaPositive lowerCut order kind C qualified accounting, ?_⟩
  exact (nativeValue_le_envelope_of_interfaces P universal count late native order kind C qualified
    accounting delta exponent deltaPositive small qualification).trans (ENNReal.ofReal_le_ofReal envelopeBound)

theorem c12Claims_of_interfaces (P : PaperProofs.Star.Parameters)
    (universal : P.UniversalFirstCurrentConstruction) (count : P.CountControllerConstruction)
    (late : P.LateRetainedConstruction) (native : P.NativeStarImplementation)
    (lowerLaw : P.ThreePricesLower) : P.C12Claims :=
  ⟨threePrices_of_interfaces P universal count late native lowerLaw, lowerLaw⟩

end PaperProofs.Star.PStarNativePrice042
