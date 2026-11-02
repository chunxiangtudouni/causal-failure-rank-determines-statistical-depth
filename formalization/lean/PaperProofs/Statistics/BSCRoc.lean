module

public import PaperProofs.Statistics.SymmetricHittingExact
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! Independent adjacent-endpoint interpolation for paid-proofs.tex:78--112.
The curve is not defined through an infimum over sequential tests. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace PaperProofs.Statistics.BinarySymmetric.Parameters

universe u

theorem endpointError_succ_lt (P : Parameters) (m : ℕ) : P.endpointError (m + 1) < P.endpointError m := by
  have ho : 0 < P.odds := zero_lt_one.trans P.odds_gt_one
  have hm : 0 < P.odds ^ m := pow_pos ho m
  unfold endpointError
  apply (div_lt_div_iff₀ (add_pos zero_lt_one (pow_pos ho _)) (add_pos zero_lt_one hm)).mpr
  rw [pow_succ]
  nlinarith [P.odds_gt_one]

theorem endpointError_strictAnti (P : Parameters) : StrictAnti P.endpointError :=
  strictAnti_nat_of_succ_lt P.endpointError_succ_lt

theorem exists_endpoint_next_le (P : Parameters) (p : ℝ) (hp : 0 < p) :
    ∃ m : ℕ, (P.endpointError (m + 1) : ℝ) ≤ p := by
  have ho : 0 < (P.odds : ℝ) := by exact_mod_cast (zero_lt_one.trans P.odds_gt_one)
  have hinv : (P.odds : ℝ)⁻¹ < 1 := (inv_lt_one₀ ho).mpr (by exact_mod_cast P.odds_gt_one)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hp hinv
  refine ⟨m, ?_⟩
  have hbound : (P.endpointError m : ℝ) ≤ ((P.odds : ℝ)⁻¹) ^ m := by
    simp only [endpointError, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_pow]
    rw [inv_pow, ← one_div]
    exact one_div_le_one_div_of_le (pow_pos ho m) (by linarith)
  have hnext : (P.endpointError (m + 1) : ℝ) ≤ (P.endpointError m : ℝ) := by
    exact_mod_cast (P.endpointError_succ_lt m).le
  exact hnext.trans (hbound.trans hm.le)

/-- Least adjacent interval with lower endpoint at most p. Real comparisons
are deliberately noncomputable; a rational search is provided below. -/
noncomputable def rocIndex (P : Parameters) (p : ℝ) (hp : 0 < p) : ℕ := by
  classical
  exact Nat.find (P.exists_endpoint_next_le p hp)

theorem rocIndex_lower (P : Parameters) (p : ℝ) (hp : 0 < p) :
    (P.endpointError (P.rocIndex p hp + 1) : ℝ) ≤ p := by
  classical
  exact Nat.find_spec (P.exists_endpoint_next_le p hp)

theorem rocIndex_min (P : Parameters) (p : ℝ) (hp : 0 < p) {m : ℕ}
    (hm : (P.endpointError (m + 1) : ℝ) ≤ p) : P.rocIndex p hp ≤ m := by
  classical
  exact Nat.find_min' (P.exists_endpoint_next_le p hp) hm

theorem rocIndex_upper (P : Parameters) (p : ℝ) (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    p ≤ (P.endpointError (P.rocIndex p hp) : ℝ) := by
  cases hn : P.rocIndex p hp with
  | zero => simpa only [P.endpointError_zero, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hhalf
  | succ n =>
    by_contra h
    have hmin := P.rocIndex_min p hp (m := n) (le_of_lt (lt_of_not_ge h))
    rw [hn] at hmin
    omega

noncomputable def rocWeight (P : Parameters) (m : ℕ) (p : ℝ) : ℝ :=
  (p - (P.endpointError (m + 1) : ℝ)) /
    ((P.endpointError m : ℝ) - (P.endpointError (m + 1) : ℝ))

theorem endpoint_gap_pos (P : Parameters) (m : ℕ) :
    0 < (P.endpointError m : ℝ) - (P.endpointError (m + 1) : ℝ) := by
  have h : (P.endpointError (m + 1) : ℝ) < (P.endpointError m : ℝ) := by
    exact_mod_cast P.endpointError_succ_lt m
  linarith

theorem rocWeight_mem_Icc (P : Parameters) (m : ℕ) (p : ℝ)
    (hlower : (P.endpointError (m + 1) : ℝ) ≤ p) (hupper : p ≤ (P.endpointError m : ℝ)) :
    P.rocWeight m p ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlower) (P.endpoint_gap_pos m).le
  · exact (div_le_one (P.endpoint_gap_pos m)).mpr (by linarith)

theorem rocWeight_error_interpolation (P : Parameters) (m : ℕ) (p : ℝ) :
    P.rocWeight m p * (P.endpointError m : ℝ) +
      (1 - P.rocWeight m p) * (P.endpointError (m + 1) : ℝ) = p := by
  unfold rocWeight
  field_simp [(P.endpoint_gap_pos m).ne']
  ring

noncomputable def rocChord (P : Parameters) (m : ℕ) (p : ℝ) : ℝ :=
  P.rocWeight m p * (P.endpointCharge m : ℝ) +
    (1 - P.rocWeight m p) * (P.endpointCharge (m + 1) : ℝ)

theorem rocChord_nonneg (P : Parameters) (m : ℕ) (p : ℝ)
    (hlower : (P.endpointError (m + 1) : ℝ) ≤ p) (hupper : p ≤ (P.endpointError m : ℝ)) :
    0 ≤ P.rocChord m p := by
  have hw := P.rocWeight_mem_Icc m p hlower hupper
  have hc (n : ℕ) : 0 ≤ (P.endpointCharge n : ℝ) := by exact_mod_cast P.endpointCharge_nonneg n
  exact add_nonneg (mul_nonneg hw.1 (hc m)) (mul_nonneg (sub_nonneg.mpr hw.2) (hc (m + 1)))

/-- The independent ROC curve g: finite adjacent interpolation on the
original error interval, and genuinely infinity at zero. -/
noncomputable def rocPrice (P : Parameters) (p : ℝ) : ℝ≥0∞ :=
  if h : 0 < p ∧ p ≤ 1 / 2 then ENNReal.ofReal (P.rocChord (P.rocIndex p h.1) p) else ⊤

@[simp] theorem rocPrice_zero (P : Parameters) : P.rocPrice 0 = ⊤ := by simp [rocPrice]

theorem rocPrice_of_pos (P : Parameters) (p : ℝ) (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    P.rocPrice p = ENNReal.ofReal (P.rocChord (P.rocIndex p hp) p) := by
  rw [rocPrice, dite_eq_left ⟨hp, hhalf⟩]

theorem rocPrice_ne_top (P : Parameters) (p : ℝ) (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    P.rocPrice p ≠ ⊤ := by
  rw [P.rocPrice_of_pos p hp hhalf]
  exact ENNReal.ofReal_ne_top

theorem exists_endpoint_next_le_rat (P : Parameters) (p : ℚ) (hp : 0 < p) :
    ∃ m : ℕ, P.endpointError (m + 1) ≤ p := by
  have hpr : 0 < (p : ℝ) := by exact_mod_cast hp
  obtain ⟨m, hm⟩ := P.exists_endpoint_next_le (p : ℝ) hpr
  exact ⟨m, by exact_mod_cast hm⟩

/-- Executable unbounded search over exact rational comparisons, with
termination established by the preceding theorem rather than an oracle. -/
def rocIndexRat (P : Parameters) (p : ℚ) (hp : 0 < p) : ℕ :=
  Nat.find (P.exists_endpoint_next_le_rat p hp)

theorem rocIndexRat_spec (P : Parameters) (p : ℚ) (hp : 0 < p) :
    P.endpointError (P.rocIndexRat p hp + 1) ≤ p :=
  Nat.find_spec (P.exists_endpoint_next_le_rat p hp)

theorem rocIndexRat_min (P : Parameters) (p : ℚ) (hp : 0 < p) {m : ℕ}
    (hm : P.endpointError (m + 1) ≤ p) : P.rocIndexRat p hp ≤ m :=
  Nat.find_min' (P.exists_endpoint_next_le_rat p hp) hm

theorem rocIndex_rat_eq (P : Parameters) (p : ℚ) (hp : 0 < p) :
    P.rocIndex (p : ℝ) (by exact_mod_cast hp) = P.rocIndexRat p hp := by
  apply Nat.le_antisymm
  · apply P.rocIndex_min
    exact_mod_cast P.rocIndexRat_spec p hp
  · apply P.rocIndexRat_min
    exact_mod_cast P.rocIndex_lower (p : ℝ) (by exact_mod_cast hp)

def rocWeightRat (P : Parameters) (m : ℕ) (p : ℚ) : ℚ :=
  (p - P.endpointError (m + 1)) / (P.endpointError m - P.endpointError (m + 1))

def rocPriceRat (P : Parameters) (p : ℚ) (hp : 0 < p) : ℚ :=
  let m := P.rocIndexRat p hp
  P.rocWeightRat m p * P.endpointCharge m + (1 - P.rocWeightRat m p) * P.endpointCharge (m + 1)

theorem rocWeightRat_cast (P : Parameters) (m : ℕ) (p : ℚ) :
    (P.rocWeightRat m p : ℝ) = P.rocWeight m (p : ℝ) := by
  simp only [rocWeightRat, rocWeight, Rat.cast_div, Rat.cast_sub]

theorem rocPrice_rat_eq (P : Parameters) (p : ℚ) (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    P.rocPrice (p : ℝ) = ENNReal.ofReal (P.rocPriceRat p hp : ℝ) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hhalfR : (p : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hhalf
    norm_num at h
    exact h
  rw [P.rocPrice_of_pos (p : ℝ) hpR hhalfR, P.rocIndex_rat_eq p hp]
  congr 1
  simp only [rocPriceRat, rocChord, Rat.cast_add, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_one, P.rocWeightRat_cast]

theorem rocIndex_endpoint_succ (P : Parameters) (m : ℕ) :
    P.rocIndex (P.endpointError (m + 1) : ℝ) (by exact_mod_cast P.endpointError_pos (m + 1)) = m := by
  have hp : 0 < (P.endpointError (m + 1) : ℝ) := by exact_mod_cast P.endpointError_pos (m + 1)
  apply Nat.le_antisymm
  · exact P.rocIndex_min _ hp le_rfl
  · by_contra h
    have hlt : P.rocIndex (P.endpointError (m + 1) : ℝ) hp < m := Nat.lt_of_not_ge h
    have he : (P.endpointError (m + 1) : ℝ) <
        (P.endpointError (P.rocIndex (P.endpointError (m + 1) : ℝ) hp + 1) : ℝ) := by
      exact_mod_cast P.endpointError_strictAnti (Nat.add_lt_add_right hlt 1)
    exact (not_le_of_gt he) (P.rocIndex_lower _ hp)

theorem rocPrice_endpoint_succ (P : Parameters) (m : ℕ) :
    P.rocPrice (P.endpointError (m + 1) : ℝ) = ENNReal.ofReal (P.endpointCharge (m + 1) : ℝ) := by
  have hp : 0 < (P.endpointError (m + 1) : ℝ) := by exact_mod_cast P.endpointError_pos (m + 1)
  have hh : (P.endpointError (m + 1) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (P.endpointError_le_half (m + 1))
    norm_num at h
    exact h
  rw [P.rocPrice_of_pos _ hp hh, P.rocIndex_endpoint_succ]
  simp only [rocChord, rocWeight, sub_self, zero_div, zero_mul, sub_zero, one_mul, zero_add]

theorem rocPrice_half (P : Parameters) : P.rocPrice (1 / 2) = 0 := by
  have hi : P.rocIndex (1 / 2) (by norm_num) = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply P.rocIndex_min
    have h := (Rat.cast_le (K := ℝ)).mpr (P.endpointError_le_half 1)
    norm_num at h
    exact h
  have hw : P.rocWeight 0 (1 / 2) = 1 := by
    have hgap := P.endpoint_gap_pos 0
    simp only [P.endpointError_zero, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hgap
    simp only [rocWeight, P.endpointError_zero, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    exact div_self hgap.ne'
  rw [P.rocPrice_of_pos _ (by norm_num) (by norm_num), hi]
  simp only [rocChord, hw, one_mul, sub_self, zero_mul, add_zero, P.endpointCharge_zero,
    Rat.cast_zero, ENNReal.ofReal_zero]

theorem rocPrice_endpoint (P : Parameters) (m : ℕ) :
    P.rocPrice (P.endpointError m : ℝ) = ENNReal.ofReal (P.endpointCharge m : ℝ) := by
  cases m with
  | zero => simpa only [P.endpointError_zero, P.endpointCharge_zero, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat, Rat.cast_zero, ENNReal.ofReal_zero] using P.rocPrice_half
  | succ m => exact P.rocPrice_endpoint_succ m

/-- An initial Bernoulli seed. Its law is independent of the hidden fact
and tape through the existing `conditionalLaw` product construction. -/
noncomputable def rocCoinLaw (weight : Set.Icc (0 : ℝ) 1) : Measure Bool :=
  ENNReal.ofReal weight.val • Measure.dirac true +
    ENNReal.ofReal (1 - weight.val) • Measure.dirac false

instance rocCoinLaw_probability (weight : Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (rocCoinLaw weight) := by
  constructor
  simp only [rocCoinLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add weight.property.1 (sub_nonneg.mpr weight.property.2)]
  norm_num

noncomputable def fairGuessLaw : Measure Bool := rocCoinLaw ⟨1 / 2, by norm_num⟩

instance fairGuessLaw_probability : IsProbabilityMeasure fairGuessLaw := by
  unfold fairGuessLaw
  infer_instance

def fairGuessTest (P : Parameters) : P.experiment.AdmissibleRule Bool where
  rule := {
    stop := fun _ _ => 0
    decision := fun seed _ => seed
    stopping := by intro seed tape tape' n _; rfl
    stoppedDecision := by intro seed tape tape' n _ _ _; rfl
  }
  measurable_stop := measurable_const
  measurable_decision := measurable_fst

theorem fairGuess_conditionalError (P : Parameters) (x : Bool) :
    P.experiment.conditionalError fairGuessLaw P.fairGuessTest x = ENNReal.ofReal (1 / 2 : ℝ) := by
  have hset : {sample : Bool × P.experiment.Tape | sample.1 ≠ x} =
      {seed : Bool | seed ≠ x} ×ˢ Set.univ := by ext sample; simp
  change (fairGuessLaw.prod (P.experiment.tapeLaw x)) {sample | sample.1 ≠ x} = _
  rw [hset, Measure.prod_prod, measure_univ, mul_one]
  cases x <;> norm_num [fairGuessLaw, rocCoinLaw]

theorem fairGuess_expectedSamples (P : Parameters) (x : Bool) :
    P.experiment.expectedSamples fairGuessLaw P.fairGuessTest x = 0 := by
  simp [BinaryExperiment.expectedSamples, fairGuessTest]

theorem fairGuess_expectedCharge (P : Parameters) (x : Bool) :
    P.experiment.expectedObservationCharge fairGuessLaw P.fairGuessTest x = 0 := by
  simp [BinaryExperiment.expectedObservationCharge, fairGuessTest]

noncomputable def hittingTestOnBool (P : Parameters) (m : ℕ) : P.experiment.AdmissibleRule Bool :=
  (fun test : P.experiment.AdmissibleRule Unit => ({
    rule := {
      stop := fun _ tape => test.rule.stop () tape
      decision := fun _ tape => test.rule.decision () tape
      stopping := by
        intro _ tape tape' n hprefix
        exact test.rule.stopping () tape tape' n hprefix
      stoppedDecision := by
        intro _ tape tape' n hs hs' hprefix
        exact test.rule.stoppedDecision () tape tape' n hs hs' hprefix
    }
    measurable_stop := by
      have hp : Measurable (fun sample : Bool × P.experiment.Tape => ((() : Unit), sample.2)) :=
        measurable_const.prodMk measurable_snd
      exact test.measurable_stop.comp hp
    measurable_decision := by
      have hp : Measurable (fun sample : Bool × P.experiment.Tape => ((() : Unit), sample.2)) :=
        measurable_const.prodMk measurable_snd
      exact test.measurable_decision.comp hp
  } : P.experiment.AdmissibleRule Bool)) (P.symmetricHittingTest m)

/-- A real endpoint test for every m. At m=0 the independent fair guess
gives each truth error 1/2, unlike deterministic MAP tie-breaking. -/
noncomputable def rocEndpointTest (P : Parameters) (m : ℕ) : P.experiment.AdmissibleRule Bool :=
  if m = 0 then P.fairGuessTest else P.hittingTestOnBool m

@[simp] theorem rocEndpointTest_zero (P : Parameters) : P.rocEndpointTest 0 = P.fairGuessTest := by
  simp only [rocEndpointTest, ↓reduceIte]

noncomputable def rocInitialWeight (P : Parameters) (p : ℝ) (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨P.rocWeight (P.rocIndex p hp) p,
    P.rocWeight_mem_Icc _ _ (P.rocIndex_lower p hp) (P.rocIndex_upper p hp hhalf)⟩

theorem rocInitialWeight_rat_eq (P : Parameters) (p : ℚ) (hp : 0 < p)
    (hhalf : (p : ℝ) ≤ 1 / 2) :
    (P.rocInitialWeight (p : ℝ) (by exact_mod_cast hp) hhalf).val =
      (P.rocWeightRat (P.rocIndexRat p hp) p : ℝ) := by
  change P.rocWeight (P.rocIndex (p : ℝ) _) (p : ℝ) = _
  rw [P.rocIndex_rat_eq p hp, P.rocWeightRat_cast]

/-- The first seed selects one adjacent endpoint before any observations;
the second independent seed is the fair guess when the chosen endpoint is 0. -/
noncomputable def adjacentMixtureTest (P : Parameters) (m : ℕ) :
    P.experiment.AdmissibleRule (Bool × Bool) :=
  (fun lower upper : P.experiment.AdmissibleRule Bool => ({
  rule := {
    stop := fun seed tape =>
      if seed.1 then lower.rule.stop seed.2 tape else upper.rule.stop seed.2 tape
    decision := fun seed tape =>
      if seed.1 then lower.rule.decision seed.2 tape else upper.rule.decision seed.2 tape
    stopping := by
      intro seed tape tape' n hprefix
      cases hb : seed.1 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte]
      · exact upper.rule.stopping seed.2 tape tape' n hprefix
      · exact lower.rule.stopping seed.2 tape tape' n hprefix
    stoppedDecision := by
      intro seed tape tape' n hs hs' hprefix
      cases hb : seed.1 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hs hs' ⊢
      · exact upper.rule.stoppedDecision seed.2 tape tape' n hs hs' hprefix
      · exact lower.rule.stoppedDecision seed.2 tape tape' n hs hs' hprefix
  }
  measurable_stop := by
    have hp : Measurable (fun sample : (Bool × Bool) × P.experiment.Tape => (sample.1.2, sample.2)) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    exact Measurable.ite ((measurable_fst.comp measurable_fst) (measurableSet_singleton true))
      (lower.measurable_stop.comp hp) (upper.measurable_stop.comp hp)
  measurable_decision := by
    have hp : Measurable (fun sample : (Bool × Bool) × P.experiment.Tape => (sample.1.2, sample.2)) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    exact Measurable.ite ((measurable_fst.comp measurable_fst) (measurableSet_singleton true))
      (lower.measurable_decision.comp hp) (upper.measurable_decision.comp hp)
  } : P.experiment.AdmissibleRule (Bool × Bool)))
    (P.rocEndpointTest m) (P.rocEndpointTest (m + 1))

noncomputable def adjacentMixtureSeedLaw (weight : Set.Icc (0 : ℝ) 1) : Measure (Bool × Bool) :=
  (rocCoinLaw weight).prod fairGuessLaw

instance adjacentMixtureSeedLaw_probability (weight : Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (adjacentMixtureSeedLaw weight) := by
  unfold adjacentMixtureSeedLaw
  infer_instance

section ArbitraryTest

variable {Seed : Type u} [MeasurableSpace Seed]

theorem roc_bayesError_ne_top (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) : P.experiment.bayesError ν test ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (P.experiment.bayesError_le_one ν test)

/-- Real error conversion is certified by the actual error ≤1 theorem;
expected observation charges are kept in ENNReal throughout. -/
noncomputable def rocBayesError (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) : Set.Icc (0 : ℝ) 1 :=
  ⟨(P.experiment.bayesError ν test).toReal, ENNReal.toReal_nonneg,
    by simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (P.experiment.bayesError_le_one ν test)⟩

theorem rocBayesError_exact (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) :
    ENNReal.ofReal (P.rocBayesError ν test).val = P.experiment.bayesError ν test :=
  ENNReal.ofReal_toReal (P.roc_bayesError_ne_top ν test)

noncomputable def adjustedBayesError (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) : ℝ :=
  min (P.rocBayesError ν test).val (1 - (P.rocBayesError ν test).val)

theorem adjustedBayesError_mem_Icc (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) : P.adjustedBayesError ν test ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have he := (P.rocBayesError ν test).property
  constructor
  · exact le_min he.1 (by linarith [he.2])
  · by_cases h : (P.rocBayesError ν test).val ≤ 1 / 2
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)

end ArbitraryTest

/-- Full original non-MAP lower-bound obligation, allowing arbitrary private
seed universes and infinite observation fees. The open error range is exactly
the one in paid-proofs.tex:84--86. No finite-ET hypothesis is added. -/
def RocArbitraryDecisionLower (P : Parameters) : Prop :=
  ∀ (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ test : P.experiment.AdmissibleRule Seed,
        0 < (P.rocBayesError ν test).val → (P.rocBayesError ν test).val < 1 →
        P.rocPrice (P.adjustedBayesError ν test) ≤ P.experiment.bayesObservationCharge ν test

/-- Outstanding attainment by this concrete initial mixture of exactly the
two selected adjacent endpoint tests, including an independent m0 fair guess. -/
def RocAdjacentMixtureAttains (P : Parameters) : Prop :=
  ∀ (p : ℝ) (hp : 0 < p) (hhalf : p ≤ 1 / 2),
    let ν := adjacentMixtureSeedLaw (P.rocInitialWeight p hp hhalf)
    let test := P.adjacentMixtureTest (P.rocIndex p hp)
    (∀ x : Bool, P.experiment.conditionalError ν test x = ENNReal.ofReal p) ∧
    (∀ x : Bool, P.experiment.expectedObservationCharge ν test x = P.rocPrice p)

/-- Outstanding MAP attainment by the same concrete adjacent mixture.
At every finite stop the decision has the posterior-log-odds optimal sign;
score zero permits either decision, including the independent m0 guess.
Combined with the independent lower bound, this states the MAP minimum. -/
def RocMAPAttains (P : Parameters) : Prop :=
  ∀ (p : ℝ) (hp : 0 < p) (hhalf : p ≤ 1 / 2),
    let ν := adjacentMixtureSeedLaw (P.rocInitialWeight p hp hhalf)
    let test := P.adjacentMixtureTest (P.rocIndex p hp)
    (∀ x : Bool, P.experiment.conditionalError ν test x = ENNReal.ofReal p) ∧
    (∀ x : Bool, P.experiment.expectedObservationCharge ν test x = P.rocPrice p) ∧
    ∀ (seed : Bool × Bool) (tape : P.experiment.Tape) (n : ℕ),
      test.rule.stop seed tape = (n : ℕ∞) →
        if test.rule.decision seed tape then 0 ≤ P.experiment.logOddsScore tape n
        else P.experiment.logOddsScore tape n ≤ 0

/-- Outstanding arbitrary-decision attainment on the original open error
range. The witness uses the same initial adjacent mixture at min(e,1-e),
and complements its decision exactly when e>1/2. The existential test must
still prove all AdmissibleRule obligations; the target is not a test field. -/
def RocArbitraryDecisionAttains (P : Parameters) : Prop :=
  ∀ (e : ℝ), 0 < e → e < 1 →
    let p := min e (1 - e)
    ∃ (hp : 0 < p) (hhalf : p ≤ 1 / 2) (ν : Measure (Bool × Bool)),
      IsProbabilityMeasure ν ∧
      ν = adjacentMixtureSeedLaw (P.rocInitialWeight p hp hhalf) ∧
      ∃ test : P.experiment.AdmissibleRule (Bool × Bool),
        let base := P.adjacentMixtureTest (P.rocIndex p hp)
        (∀ seed tape, test.rule.stop seed tape = base.rule.stop seed tape) ∧
        (∀ seed tape, test.rule.decision seed tape =
          if e ≤ 1 / 2 then base.rule.decision seed tape else !(base.rule.decision seed tape)) ∧
        P.experiment.bayesError ν test = ENNReal.ofReal e ∧
        P.experiment.bayesObservationCharge ν test = P.rocPrice p

/-- Full D05 statement package, still unproved: arbitrary-decision lower
bound, MAP minimum attainment, and the complementary decision witnesses.
The lower-bound seed universe remains unrestricted. -/
def ExactROCClaims (P : Parameters) : Prop :=
  RocArbitraryDecisionLower.{u} P ∧ P.RocMAPAttains ∧ P.RocArbitraryDecisionAttains

end PaperProofs.Statistics.BinarySymmetric.Parameters
