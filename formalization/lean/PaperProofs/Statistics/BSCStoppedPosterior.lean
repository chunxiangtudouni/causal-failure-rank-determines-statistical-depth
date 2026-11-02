module

public import PaperProofs.Statistics.SymmetricHittingExact

/-!
Neutral BSC posterior information, frozen star-proofs.tex:40--56 and
paid-proofs.tex:38--68. Posterior error is defined from the actual stopped
word likelihoods, independently of the test's possibly non-MAP decision.
The infinity branch is explicit and is never mapped to the empty word.
Pre-birth gates are measurable subsets of the independent private seed;
they cannot inspect the current hidden truth or its review tape.

The independent proposition interfaces below are proved from the actual
posterior density and Wald. Their finite-ET hypothesis belongs only to the
information identity, never to the class of admissible tests or the full
comparison infimum. Restricted identities require finite ET only on the gate.
-/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace PaperProofs.Statistics.BinarySymmetric

theorem phiReal_le_log_inv {p : ℝ} (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    phiReal p ≤ Real.log (1 / p) := by
  have hq : 0 < 1 - p := by linarith
  have hlogq : Real.log (1 - p) ≤ 0 := Real.log_nonpos hq.le (by linarith)
  have hlogp : 0 ≤ Real.log (1 / p) :=
    Real.log_nonneg ((le_div_iff₀ hp).mpr (by linarith))
  have hfactor : 0 ≤ 1 - 2 * p := by linarith
  have hsum : Real.log ((1 - p) / p) = Real.log (1 - p) + Real.log (1 / p) := by
    rw [Real.log_div hq.ne' hp.ne', one_div, Real.log_inv]
    ring
  rw [phiReal, hsum]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hfactor hlogq, mul_nonneg hp.le hlogp]

theorem log_inv_sub_two_le_phiReal {p : ℝ} (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    Real.log (1 / p) - 2 ≤ phiReal p := by
  have hq : 0 < 1 - p := by linarith
  have hlogq : 0 ≤ -Real.log (1 - p) := neg_nonneg.mpr (Real.log_nonpos hq.le (by linarith))
  have hplog : p * Real.log (1 / p) ≤ 1 - p := by
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (one_div_pos.mpr hp)) hp.le
    have heq : p * (1 / p - 1) = 1 - p := by field_simp
    rwa [heq] at h
  have hqlog : (1 - p) * (-Real.log (1 - p)) ≤ p := by
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (inv_pos.mpr hq)) hq.le
    rw [Real.log_inv] at h
    have heq : (1 - p) * ((1 - p)⁻¹ - 1) = p := by field_simp; ring
    rwa [heq] at h
  have hterm : (1 - 2 * p) * (-Real.log (1 - p)) ≤ p :=
    (mul_le_mul_of_nonneg_right (by linarith : 1 - 2 * p ≤ 1 - p) hlogq).trans hqlog
  have hsum : Real.log ((1 - p) / p) = Real.log (1 - p) + Real.log (1 / p) := by
    rw [Real.log_div hq.ne' hp.ne', one_div, Real.log_inv]
    ring
  rw [phiReal, hsum]
  nlinarith

/-- Finite positive word likelihoods give the conditional oriented-score
formula; this algebra does not mention a sampling or output decision rule. -/
theorem phiReal_min_likelihoods (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    phiReal (min (u / (u + v)) (v / (u + v))) =
      ((v - u) / (u + v)) * Real.log (v / u) := by
  have hs : 0 < u + v := add_pos hu hv
  by_cases huv : u ≤ v
  · rw [min_eq_left ((div_le_div_iff_of_pos_right hs).mpr huv), phiReal]
    have hr : (1 - u / (u + v)) / (u / (u + v)) = v / u := by field_simp; ring
    rw [hr]
    congr 1
    field_simp
    ring
  · have hvu : v ≤ u := (lt_of_not_ge huv).le
    rw [min_eq_right ((div_le_div_iff_of_pos_right hs).mpr hvu), phiReal]
    have hr : (1 - v / (u + v)) / (v / (u + v)) = u / v := by field_simp; ring
    have hl : Real.log (u / v) = -Real.log (v / u) := by
      rw [Real.log_div hu.ne' hv.ne', Real.log_div hv.ne' hu.ne']
      ring
    rw [hr, hl]
    field_simp
    ring

namespace Parameters

universe u

private theorem ofReal_half : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem priorMass_eq_half (P : Parameters) (x : Bool) :
    P.experiment.priorMass x = (1 / 2 : ℝ≥0∞) := by
  change ENNReal.ofReal (P.experiment.prior x : ℝ) = _
  rw [P.prior_eq_half]
  push_cast
  exact ofReal_half

noncomputable def wordEvidence (P : Parameters) (word : P.experiment.StoppedWord) : ℝ :=
  P.experiment.wordProbability false word + P.experiment.wordProbability true word

theorem wordEvidence_pos (P : Parameters) (word : P.experiment.StoppedWord) :
    0 < P.wordEvidence word :=
  add_pos (P.experiment.wordProbability_pos false word) (P.experiment.wordProbability_pos true word)

/-- Fair-prior Bayes posterior mass, using both actual finite-word likelihoods.
Private-seed/stopping factors cancel by the true transcript density theorem. -/
noncomputable def wordPosteriorMass (P : Parameters) (x : Bool)
    (word : P.experiment.StoppedWord) : ℝ :=
  P.experiment.wordProbability x word / P.wordEvidence word

noncomputable def wordPosteriorError (P : Parameters) (word : P.experiment.StoppedWord) : ℝ :=
  min (P.wordPosteriorMass false word) (P.wordPosteriorMass true word)

theorem wordPosteriorMass_pos (P : Parameters) (x : Bool) (word : P.experiment.StoppedWord) :
    0 < P.wordPosteriorMass x word :=
  div_pos (P.experiment.wordProbability_pos x word) (P.wordEvidence_pos word)

theorem wordPosteriorMass_sum (P : Parameters) (word : P.experiment.StoppedWord) :
    P.wordPosteriorMass false word + P.wordPosteriorMass true word = 1 := by
  rw [wordPosteriorMass, wordPosteriorMass, ← add_div]
  exact div_self (P.wordEvidence_pos word).ne'

theorem wordPosteriorError_pos (P : Parameters) (word : P.experiment.StoppedWord) :
    0 < P.wordPosteriorError word :=
  lt_min (P.wordPosteriorMass_pos false word) (P.wordPosteriorMass_pos true word)

theorem wordPosteriorError_le_half (P : Parameters) (word : P.experiment.StoppedWord) :
    P.wordPosteriorError word ≤ 1 / 2 := by
  have hs := P.wordPosteriorMass_sum word
  by_cases h : P.wordPosteriorMass false word ≤ 1 / 2
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem wordPosteriorError_empty (P : Parameters) :
    P.wordPosteriorError ⟨0, Fin.elim0⟩ = 1 / 2 := by
  norm_num [wordPosteriorError, wordPosteriorMass, wordEvidence, BinaryExperiment.wordProbability]

theorem wordPosterior_phi_eq_orientedScore (P : Parameters) (word : P.experiment.StoppedWord) :
    phiReal (P.wordPosteriorError word) =
      P.wordPosteriorMass false word * P.experiment.wordLogLikelihood false word +
      P.wordPosteriorMass true word * P.experiment.wordLogLikelihood true word := by
  have hscalar := phiReal_min_likelihoods _ _ (P.experiment.wordProbability_pos false word)
    (P.experiment.wordProbability_pos true word)
  have hl : Real.log (P.experiment.wordProbability true word / P.experiment.wordProbability false word) =
      P.experiment.wordLogLikelihood true word := by
    have h := P.experiment.log_wordLikelihood true word
    rw [P.experiment.wordLikelihood_eq_div] at h
    exact h
  rw [hl] at hscalar
  change phiReal (P.wordPosteriorError word) = _ at hscalar
  rw [hscalar, P.wordLogLikelihood_false_eq_neg_true]
  unfold wordPosteriorMass wordEvidence
  ring

section Seed

variable {Seed : Type u} [MeasurableSpace Seed]

/-- The actual fair mixture of the two existing stopped-transcript laws. -/
noncomputable def bayesStoppedLaw (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) : Measure (Seed × P.experiment.StoppedWord) :=
  (1 / 2 : ℝ≥0∞) • P.experiment.transcriptLaw ν test false +
    (1 / 2 : ℝ≥0∞) • P.experiment.transcriptLaw ν test true

theorem bayesStoppedLaw_rectangle (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed)
    (hfinite : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤)
    (seeds : Set Seed) (hs : MeasurableSet seeds) (word : P.experiment.StoppedWord) :
    P.bayesStoppedLaw ν test (seeds ×ˢ {word}) =
      ν (seeds ∩ P.experiment.stoppingSeeds test word) * ENNReal.ofReal (P.wordEvidence word / 2) := by
  rw [bayesStoppedLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    P.experiment.transcriptLaw_rectangle_singleton ν test false (hfinite false) seeds hs word,
    P.experiment.transcriptLaw_rectangle_singleton ν test true (hfinite true) seeds hs word]
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := ofReal_half.symm
  have hadd : (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (P.experiment.wordProbability false word) +
      (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (P.experiment.wordProbability true word) =
      ENNReal.ofReal (P.wordEvidence word / 2) := by
    rw [hhalf, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_add
        (mul_nonneg (by norm_num) (P.experiment.wordProbability_pos false word).le)
        (mul_nonneg (by norm_num) (P.experiment.wordProbability_pos true word).le)]
    congr 1
    unfold wordEvidence
    ring
  calc
    _ = ν (seeds ∩ P.experiment.stoppingSeeds test word) *
        ((1 / 2 : ℝ≥0∞) * ENNReal.ofReal (P.experiment.wordProbability false word) +
          (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (P.experiment.wordProbability true word)) := by
      simp only [smul_eq_mul]
      ring
    _ = _ := by rw [hadd]

theorem wordPosterior_rectangle_bayes (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed)
    (hfinite : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤)
    (seeds : Set Seed) (hs : MeasurableSet seeds) (word : P.experiment.StoppedWord) (x : Bool) :
    ENNReal.ofReal (P.wordPosteriorMass x word) * P.bayesStoppedLaw ν test (seeds ×ˢ {word}) =
      (1 / 2 : ℝ≥0∞) * P.experiment.transcriptLaw ν test x (seeds ×ˢ {word}) := by
  rw [P.bayesStoppedLaw_rectangle ν test hfinite seeds hs word,
    P.experiment.transcriptLaw_rectangle_singleton ν test x (hfinite x) seeds hs word]
  have hreal : P.wordPosteriorMass x word * (P.wordEvidence word / 2) =
      (1 / 2 : ℝ) * P.experiment.wordProbability x word := by
    unfold wordPosteriorMass
    field_simp [(P.wordEvidence_pos word).ne']
  calc
    _ = ν (seeds ∩ P.experiment.stoppingSeeds test word) *
        ENNReal.ofReal (P.wordPosteriorMass x word * (P.wordEvidence word / 2)) := by
      rw [ENNReal.ofReal_mul (P.wordPosteriorMass_pos x word).le]
      ring
    _ = _ := by
      rw [hreal, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [ofReal_half]
      ring

/-- The finite-word formula is the actual Bayes posterior, including the
private seed in the stopped record. This is a full measure identity, proved
from genuine transcript masses rather than postulated as a posterior axiom. -/
theorem bayesStoppedLaw_posterior_withDensity (P : Parameters) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : P.experiment.AdmissibleRule Seed)
    (hfinite : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤) (x : Bool) :
    (P.bayesStoppedLaw ν test).withDensity
      (fun record => ENNReal.ofReal (P.wordPosteriorMass x record.2)) =
      (1 / 2 : ℝ≥0∞) • P.experiment.transcriptLaw ν test x := by
  have : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • P.experiment.transcriptLaw ν test x) :=
    ⟨by norm_num [Measure.smul_apply, smul_eq_mul]⟩
  symm
  apply Measure.ext_prod
  intro seeds words hs _hw
  have hset : seeds ×ˢ words = ⋃ word : words, seeds ×ˢ {word.val} := by
    ext record
    simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hs', hw'⟩
      exact ⟨⟨record.2, hw'⟩, hs', rfl⟩
    · rintro ⟨word, hs', hw'⟩
      exact ⟨hs', hw' ▸ word.property⟩
  have hdisj : Pairwise (fun word word' : words => Disjoint (seeds ×ˢ {word.val}) (seeds ×ˢ {word'.val})) := by
    intro word word' hne
    apply Set.disjoint_left.mpr
    intro record hr hr'
    exact hne (Subtype.ext (hr.2.symm.trans hr'.2))
  have hm (word : words) : MeasurableSet (seeds ×ˢ {word.val}) :=
    hs.prod (measurableSet_singleton word.val)
  rw [hset, measure_iUnion hdisj hm, measure_iUnion hdisj hm]
  apply tsum_congr
  intro word
  rw [Measure.smul_apply, withDensity_apply _ (hm word)]
  have hconstant : ∫⁻ record in seeds ×ˢ {word.val}, ENNReal.ofReal (P.wordPosteriorMass x record.2)
      ∂(P.bayesStoppedLaw ν test) =
      ENNReal.ofReal (P.wordPosteriorMass x word.val) * P.bayesStoppedLaw ν test (seeds ×ˢ {word.val}) := by
    calc
      _ = ∫⁻ _record in seeds ×ˢ {word.val}, ENNReal.ofReal (P.wordPosteriorMass x word.val)
          ∂(P.bayesStoppedLaw ν test) := by
        apply setLIntegral_congr_fun (hm word)
        intro record hr
        change ENNReal.ofReal (P.wordPosteriorMass x record.2) =
          ENNReal.ofReal (P.wordPosteriorMass x word.val)
        rw [hr.2]
      _ = _ := by simp
  rw [hconstant]
  exact (P.wordPosterior_rectangle_bayes ν test hfinite seeds hs word.val x).symm

/-- No claimed posterior is assigned at an infinite stopping time. Its
extended information charge is infinity, rather than the empty-word value. -/
noncomputable def stoppedPosteriorInformation (P : Parameters)
    (test : P.experiment.AdmissibleRule Seed) (sample : Seed × P.experiment.Tape) : ℝ≥0∞ :=
  if test.rule.stop sample.1 sample.2 = ⊤ then ⊤
  else phi (P.wordPosteriorError (P.experiment.stoppedTranscript test sample).2)

theorem stoppedPosteriorInformation_of_finite (P : Parameters)
    (test : P.experiment.AdmissibleRule Seed) (sample : Seed × P.experiment.Tape)
    (hs : test.rule.stop sample.1 sample.2 ≠ ⊤) :
    P.stoppedPosteriorInformation test sample =
      phi (P.wordPosteriorError (P.experiment.stoppedTranscript test sample).2) := by
  simp only [stoppedPosteriorInformation, hs, ↓reduceIte]

theorem stoppedPosteriorInformation_of_infinite (P : Parameters)
    (test : P.experiment.AdmissibleRule Seed) (sample : Seed × P.experiment.Tape)
    (hs : test.rule.stop sample.1 sample.2 = ⊤) :
    P.stoppedPosteriorInformation test sample = ⊤ := by
  simp only [stoppedPosteriorInformation, hs, ↓reduceIte]

theorem measurable_stoppedPosteriorInformation (P : Parameters)
    (test : P.experiment.AdmissibleRule Seed) : Measurable (P.stoppedPosteriorInformation test) := by
  exact measurable_const.ite ((measurableSet_singleton (⊤ : ℕ∞)).preimage test.measurable_stop)
    ((measurable_of_countable (fun word => phi (P.wordPosteriorError word))).comp
      (P.experiment.measurable_stoppedTranscript test).snd)

noncomputable def expectedPosteriorInformation (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) : ℝ≥0∞ :=
  ∑ x : Bool, P.experiment.priorMass x *
    ∫⁻ sample, P.stoppedPosteriorInformation test sample ∂(P.experiment.conditionalLaw ν x)

theorem priorWeighted_ne_top_iff (P : Parameters) (f : Bool → ℝ≥0∞) :
    (∑ x : Bool, P.experiment.priorMass x * f x) ≠ ⊤ ↔ ∀ x, f x ≠ ⊤ := by
  constructor
  · intro h x htop
    have hterm := ENNReal.sum_ne_top.mp h x (Finset.mem_univ x)
    have hp : P.experiment.priorMass x ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (P.experiment.priorReal_pos x))
    apply hterm
    simp [htop, hp]
  · intro h
    apply ENNReal.sum_ne_top.mpr
    intro x _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (h x)

/-- The source's actual fair-Bayes expected observation count. -/
noncomputable def bayesExpectedSamples (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) : ℝ≥0∞ :=
  ∑ x : Bool, P.experiment.priorMass x * P.experiment.expectedSamples ν test x

theorem bayesExpectedSamples_ne_top_iff (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) :
    P.bayesExpectedSamples ν test ≠ ⊤ ↔ ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤ :=
  P.priorWeighted_ne_top_iff _

/-- Only an independent-seed event may act as a pre-birth gate. In
particular eventual success is not a possible argument of this interface. -/
def preBirthGate (P : Parameters) (seeds : Set Seed) : Set (Seed × P.experiment.Tape) :=
  Prod.fst ⁻¹' seeds

theorem measurableSet_preBirthGate (P : Parameters) (seeds : Set Seed) (hs : MeasurableSet seeds) :
    MeasurableSet (P.preBirthGate seeds) := hs.preimage measurable_fst

/-- Run the supplied test on the pre-birth seed event and fill blindly
outside it. This is a real causal test, not a conditioned success policy. -/
noncomputable def preBirthTest (P : Parameters) (test : P.experiment.AdmissibleRule Seed)
    (seeds : Set Seed) (hs : MeasurableSet seeds) : P.experiment.AdmissibleRule Seed := by
  classical
  exact {
    rule := {
      stop := fun seed tape => if seed ∈ seeds then test.rule.stop seed tape else 0
      decision := fun seed tape => if seed ∈ seeds then test.rule.decision seed tape else false
      stopping := by
        intro seed tape tape' n hprefix
        by_cases h : seed ∈ seeds
        · simpa only [h, ↓reduceIte] using test.rule.stopping seed tape tape' n hprefix
        · simp only [h, ↓reduceIte]
      stoppedDecision := by
        intro seed tape tape' n hstop hstop' hprefix
        by_cases h : seed ∈ seeds
        · simp only [h, ↓reduceIte] at hstop hstop' ⊢
          exact test.rule.stoppedDecision seed tape tape' n hstop hstop' hprefix
        · simp only [h, ↓reduceIte]
    }
    measurable_stop := test.measurable_stop.ite (P.measurableSet_preBirthGate seeds hs) measurable_const
    measurable_decision := test.measurable_decision.ite (P.measurableSet_preBirthGate seeds hs) measurable_const
  }

noncomputable def gatedExpectedSamples (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed) (x : Bool) : ℝ≥0∞ :=
  ∫⁻ sample in P.preBirthGate seeds, BinaryExperiment.sampleCountENNReal (test.rule.stop sample.1 sample.2)
    ∂(P.experiment.conditionalLaw ν x)

noncomputable def gatedBayesExpectedSamples (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed) : ℝ≥0∞ :=
  ∑ x : Bool, P.experiment.priorMass x * P.gatedExpectedSamples ν test seeds x

theorem gatedBayesExpectedSamples_ne_top_iff (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed) :
    P.gatedBayesExpectedSamples ν test seeds ≠ ⊤ ↔ ∀ x, P.gatedExpectedSamples ν test seeds x ≠ ⊤ :=
  P.priorWeighted_ne_top_iff _

theorem preBirthTest_expectedSamples_eq (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed) (hs : MeasurableSet seeds) (x : Bool) :
    P.experiment.expectedSamples ν (P.preBirthTest test seeds hs) x = P.gatedExpectedSamples ν test seeds x := by
  classical
  rw [BinaryExperiment.expectedSamples, gatedExpectedSamples,
    ← lintegral_indicator (P.measurableSet_preBirthGate seeds hs)]
  apply lintegral_congr
  intro sample
  by_cases h : sample.1 ∈ seeds <;> simp [preBirthTest, preBirthGate, h]

theorem stoppedPosteriorInformation_zero_of_stop_zero (P : Parameters)
    (test : P.experiment.AdmissibleRule Seed) (sample : Seed × P.experiment.Tape)
    (hs : test.rule.stop sample.1 sample.2 = 0) : P.stoppedPosteriorInformation test sample = 0 := by
  have hw : (P.experiment.stoppedTranscript test sample).2 = ⟨0, Fin.elim0⟩ := by
    apply (P.experiment.stoppedWord_eq_iff test sample 0 Fin.elim0).mpr
    exact ⟨by rw [hs]; rfl, fun k => Fin.elim0 k⟩
  rw [P.stoppedPosteriorInformation_of_finite test sample (by rw [hs]; simp), hw,
    P.wordPosteriorError_empty, phi_half]

theorem preBirthTest_information_indicator (P : Parameters)
    (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed) (hs : MeasurableSet seeds)
    (sample : Seed × P.experiment.Tape) :
    P.stoppedPosteriorInformation (P.preBirthTest test seeds hs) sample =
      (P.preBirthGate seeds).indicator (P.stoppedPosteriorInformation test) sample := by
  classical
  by_cases h : sample.1 ∈ seeds
  · rw [Set.indicator_of_mem (show sample ∈ P.preBirthGate seeds from h)]
    have hstop : (P.preBirthTest test seeds hs).rule.stop sample.1 sample.2 = test.rule.stop sample.1 sample.2 := by
      simp only [preBirthTest, h, ↓reduceIte]
    have hword : (P.experiment.stoppedTranscript (P.preBirthTest test seeds hs) sample).2 =
        (P.experiment.stoppedTranscript test sample).2 := by
      change (⟨((P.preBirthTest test seeds hs).rule.stop sample.1 sample.2).toNat,
        fun k => sample.2 k.val⟩ : P.experiment.StoppedWord) =
        ⟨(test.rule.stop sample.1 sample.2).toNat, fun k => sample.2 k.val⟩
      rw [hstop]
    unfold stoppedPosteriorInformation
    rw [hstop, hword]
  · rw [Set.indicator_of_notMem (show sample ∉ P.preBirthGate seeds from h)]
    apply P.stoppedPosteriorInformation_zero_of_stop_zero
    simp only [preBirthTest, h, ↓reduceIte]

theorem conditionalLaw_restrict_preBirthGate (P : Parameters) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (seeds : Set Seed) (x : Bool) :
    (P.experiment.conditionalLaw ν x).restrict (P.preBirthGate seeds) =
      (ν.restrict seeds).prod (P.experiment.tapeLaw x) := by
  have heq : P.preBirthGate seeds = seeds ×ˢ (Set.univ : Set P.experiment.Tape) := by
    ext sample
    simp [preBirthGate]
  rw [heq, BinaryExperiment.conditionalLaw, ← Measure.restrict_prod_eq_prod_univ]

noncomputable def gatedObservationCharge (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed) : ℝ≥0∞ :=
  ∑ x : Bool, P.experiment.priorMass x *
    ∫⁻ sample in P.preBirthGate seeds, P.experiment.observationCharge (test.rule.stop sample.1 sample.2)
      ∂(P.experiment.conditionalLaw ν x)

noncomputable def gatedPosteriorInformation (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed) : ℝ≥0∞ :=
  ∑ x : Bool, P.experiment.priorMass x *
    ∫⁻ sample in P.preBirthGate seeds, P.stoppedPosteriorInformation test sample
      ∂(P.experiment.conditionalLaw ν x)

theorem preBirthTest_bayesObservationCharge_eq (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed) (hs : MeasurableSet seeds) :
    P.experiment.bayesObservationCharge ν (P.preBirthTest test seeds hs) = P.gatedObservationCharge ν test seeds := by
  classical
  unfold BinaryExperiment.bayesObservationCharge gatedObservationCharge
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [BinaryExperiment.expectedObservationCharge, ← lintegral_indicator (P.measurableSet_preBirthGate seeds hs)]
  apply lintegral_congr
  intro sample
  by_cases h : sample.1 ∈ seeds <;> simp [preBirthTest, preBirthGate, h]

theorem preBirthTest_expectedPosteriorInformation_eq (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed) (hs : MeasurableSet seeds) :
    P.expectedPosteriorInformation ν (P.preBirthTest test seeds hs) = P.gatedPosteriorInformation ν test seeds := by
  unfold expectedPosteriorInformation gatedPosteriorInformation
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [← lintegral_indicator (P.measurableSet_preBirthGate seeds hs)]
  exact lintegral_congr (P.preBirthTest_information_indicator test seeds hs)

@[simp] theorem gatedObservationCharge_univ (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) :
    P.gatedObservationCharge ν test Set.univ = P.experiment.bayesObservationCharge ν test := by
  simp [gatedObservationCharge, preBirthGate, BinaryExperiment.bayesObservationCharge,
    BinaryExperiment.expectedObservationCharge]

@[simp] theorem gatedPosteriorInformation_univ (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) :
    P.gatedPosteriorInformation ν test Set.univ = P.expectedPosteriorInformation ν test := by
  simp [gatedPosteriorInformation, preBirthGate, expectedPosteriorInformation]

theorem expectedPosteriorInformation_eq_stoppedLaw (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed)
    (hfinite : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤) :
    P.expectedPosteriorInformation ν test =
      ∫⁻ record : Seed × P.experiment.StoppedWord, phi (P.wordPosteriorError record.2)
        ∂(P.bayesStoppedLaw ν test) := by
  have hx (x : Bool) : (∫⁻ sample, P.stoppedPosteriorInformation test sample ∂(P.experiment.conditionalLaw ν x)) =
      ∫⁻ record : Seed × P.experiment.StoppedWord, phi (P.wordPosteriorError record.2)
        ∂(P.experiment.transcriptLaw ν test x) := by
    have hm : Measurable (fun record : Seed × P.experiment.StoppedWord => phi (P.wordPosteriorError record.2)) :=
      (measurable_of_countable (fun word => phi (P.wordPosteriorError word))).comp measurable_snd
    rw [BinaryExperiment.transcriptLaw,
      lintegral_map hm (P.experiment.measurable_stoppedTranscript test)]
    apply lintegral_congr_ae
    filter_upwards [P.experiment.expectedSamples_finite_stop ν test x (hfinite x)] with sample hs
    exact P.stoppedPosteriorInformation_of_finite test sample hs
  simp only [expectedPosteriorInformation, P.priorMass_eq_half, hx, Fintype.sum_bool,
    bayesStoppedLaw, lintegral_add_measure, lintegral_smul_measure, smul_eq_mul]
  ac_rfl

theorem posteriorWeightedLLR_integrable (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed)
    (hfinite : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤) (x : Bool) :
    Integrable (fun record : Seed × P.experiment.StoppedWord =>
      P.wordPosteriorMass x record.2 * P.experiment.wordLogLikelihood x record.2)
      (P.bayesStoppedLaw ν test) := by
  have hm : Measurable (fun record : Seed × P.experiment.StoppedWord =>
      ENNReal.ofReal (P.wordPosteriorMass x record.2)) :=
    (measurable_of_countable (fun word => ENNReal.ofReal (P.wordPosteriorMass x word))).comp measurable_snd
  have ht : ∀ᵐ record ∂(P.bayesStoppedLaw ν test),
      ENNReal.ofReal (P.wordPosteriorMass x record.2) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hi : Integrable (fun record : Seed × P.experiment.StoppedWord =>
      P.experiment.wordLogLikelihood x record.2)
      ((P.bayesStoppedLaw ν test).withDensity (fun record => ENNReal.ofReal (P.wordPosteriorMass x record.2))) := by
    rw [P.bayesStoppedLaw_posterior_withDensity ν test hfinite x]
    exact (P.experiment.integrable_wordLogLikelihood_transcriptLaw ν test x (hfinite x)).smul_measure (by norm_num)
  have h := (integrable_withDensity_iff_integrable_smul' hm ht).mp hi
  simpa only [ENNReal.toReal_ofReal (P.wordPosteriorMass_pos x _).le, smul_eq_mul] using h

theorem integral_posteriorWeightedLLR (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed)
    (hfinite : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤) (x : Bool) :
    (∫ record : Seed × P.experiment.StoppedWord,
      P.wordPosteriorMass x record.2 * P.experiment.wordLogLikelihood x record.2 ∂(P.bayesStoppedLaw ν test)) =
      (1 / 2 : ℝ) * P.kappa * (P.experiment.expectedSamples ν test x).toReal := by
  have hm : Measurable (fun record : Seed × P.experiment.StoppedWord =>
      ENNReal.ofReal (P.wordPosteriorMass x record.2)) :=
    (measurable_of_countable (fun word => ENNReal.ofReal (P.wordPosteriorMass x word))).comp measurable_snd
  have ht : ∀ᵐ record ∂(P.bayesStoppedLaw ν test),
      ENNReal.ofReal (P.wordPosteriorMass x record.2) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have h := integral_withDensity_eq_integral_toReal_smul hm ht
    (fun record : Seed × P.experiment.StoppedWord => P.experiment.wordLogLikelihood x record.2)
  rw [P.bayesStoppedLaw_posterior_withDensity ν test hfinite x, integral_smul_measure] at h
  have hw : (∫ record : Seed × P.experiment.StoppedWord,
      P.experiment.wordLogLikelihood x record.2 ∂(P.experiment.transcriptLaw ν test x)) =
      P.kappa * (P.experiment.expectedSamples ν test x).toReal := by
    have hm' : Measurable (fun record : Seed × P.experiment.StoppedWord => P.experiment.wordLogLikelihood x record.2) :=
      (measurable_of_countable (P.experiment.wordLogLikelihood x)).comp measurable_snd
    rw [BinaryExperiment.transcriptLaw,
      integral_map (P.experiment.measurable_stoppedTranscript test).aemeasurable
        hm'.aestronglyMeasurable,
      P.experiment.integral_stoppedSum_wald ν test x (hfinite x), P.divergence_eq_kappa]
  rw [hw] at h
  simpa only [ENNReal.toReal_ofReal (P.wordPosteriorMass_pos x _).le,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul, mul_assoc] using h.symm

theorem posteriorPhi_integrable (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed)
    (hfinite : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤) :
    Integrable (fun record : Seed × P.experiment.StoppedWord => phiReal (P.wordPosteriorError record.2))
      (P.bayesStoppedLaw ν test) := by
  apply ((P.posteriorWeightedLLR_integrable ν test hfinite false).add
    (P.posteriorWeightedLLR_integrable ν test hfinite true)).congr
  exact ae_of_all _ fun record => (P.wordPosterior_phi_eq_orientedScore record.2).symm

theorem integral_posteriorPhi (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed)
    (hfinite : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤) :
    (∫ record : Seed × P.experiment.StoppedWord, phiReal (P.wordPosteriorError record.2)
      ∂(P.bayesStoppedLaw ν test)) =
      P.kappa * ((1 / 2 : ℝ) * (P.experiment.expectedSamples ν test false).toReal +
        (1 / 2 : ℝ) * (P.experiment.expectedSamples ν test true).toReal) := by
  simp_rw [P.wordPosterior_phi_eq_orientedScore]
  rw [integral_add (P.posteriorWeightedLLR_integrable ν test hfinite false)
    (P.posteriorWeightedLLR_integrable ν test hfinite true),
    P.integral_posteriorWeightedLLR ν test hfinite false, P.integral_posteriorWeightedLLR ν test hfinite true]
  ring

/-- The unconditional C03/D03 expectation identity, proved from the actual
posterior density plus Wald, and retaining ENNReal on both sides. -/
theorem bayesObservationCharge_eq_posteriorInformation (P : Parameters) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : P.experiment.AdmissibleRule Seed)
    (hfinite : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤) :
    P.experiment.bayesObservationCharge ν test = ENNReal.ofReal P.a * P.expectedPosteriorInformation ν test := by
  have hinfo : P.expectedPosteriorInformation ν test =
      ENNReal.ofReal (P.kappa * ((1 / 2 : ℝ) * (P.experiment.expectedSamples ν test false).toReal +
        (1 / 2 : ℝ) * (P.experiment.expectedSamples ν test true).toReal)) := by
    rw [P.expectedPosteriorInformation_eq_stoppedLaw ν test hfinite]
    simp_rw [phi_of_pos (P.wordPosteriorError_pos _)]
    rw [← ofReal_integral_eq_lintegral_ofReal (P.posteriorPhi_integrable ν test hfinite)
      (ae_of_all _ fun record => phiReal_nonneg (P.wordPosteriorError_pos record.2)
        (P.wordPosteriorError_le_half record.2)), P.integral_posteriorPhi ν test hfinite]
  have hc (x : Bool) : P.experiment.expectedObservationCharge ν test x =
      ENNReal.ofReal ((P.reviewFee : ℝ) * (P.experiment.expectedSamples ν test x).toReal) := by
    calc
      _ = ENNReal.ofReal (P.experiment.observationFee : ℝ) * P.experiment.expectedSamples ν test x :=
        P.experiment.expectedObservationCharge_eq ν test x
      _ = ENNReal.ofReal (P.experiment.observationFee : ℝ) *
          ENNReal.ofReal (P.experiment.expectedSamples ν test x).toReal := by rw [ENNReal.ofReal_toReal (hfinite x)]
      _ = _ := (ENNReal.ofReal_mul P.experiment.observationFee_real_pos.le).symm
  rw [hinfo, ← ENNReal.ofReal_mul P.a_pos.le]
  have ha : P.a * P.kappa = (P.reviewFee : ℝ) := by
    unfold a
    exact div_mul_cancel₀ _ P.kappa_pos.ne'
  have hr : P.a * (P.kappa * ((1 / 2 : ℝ) * (P.experiment.expectedSamples ν test false).toReal +
      (1 / 2 : ℝ) * (P.experiment.expectedSamples ν test true).toReal)) =
      (1 / 2 : ℝ) * ((P.reviewFee : ℝ) * (P.experiment.expectedSamples ν test false).toReal) +
      (1 / 2 : ℝ) * ((P.reviewFee : ℝ) * (P.experiment.expectedSamples ν test true).toReal) := by
    rw [← mul_assoc, ha]
    ring
  rw [hr]
  unfold BinaryExperiment.bayesObservationCharge
  simp only [P.priorMass_eq_half, hc, Fintype.sum_bool]
  rw [← ofReal_half,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_add
      (mul_nonneg (by norm_num) (mul_nonneg (by exact_mod_cast P.reviewFee_pos.le) ENNReal.toReal_nonneg))
      (mul_nonneg (by norm_num) (mul_nonneg (by exact_mod_cast P.reviewFee_pos.le) ENNReal.toReal_nonneg))]
  congr 1
  ring

/-- Restrict only to the independent pre-birth event. Finite ET is required
ON THAT EVENT alone: the original test may have infinite ET outside it.
The zero-probability case needs no division or normalized conditional law. -/
theorem gatedObservationCharge_eq_posteriorInformation (P : Parameters) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : P.experiment.AdmissibleRule Seed)
    (seeds : Set Seed) (hs : MeasurableSet seeds)
    (hfinite : ∀ x, P.gatedExpectedSamples ν test seeds x ≠ ⊤) :
    P.gatedObservationCharge ν test seeds = ENNReal.ofReal P.a * P.gatedPosteriorInformation ν test seeds := by
  have hf (x : Bool) : P.experiment.expectedSamples ν (P.preBirthTest test seeds hs) x ≠ ⊤ := by
    rw [P.preBirthTest_expectedSamples_eq ν test seeds hs x]
    exact hfinite x
  have h := P.bayesObservationCharge_eq_posteriorInformation ν (P.preBirthTest test seeds hs) hf
  rwa [P.preBirthTest_bayesObservationCharge_eq ν test seeds hs,
    P.preBirthTest_expectedPosteriorInformation_eq ν test seeds hs] at h

theorem bayesObservationCharge_eq_posteriorInformation_of_finite_bayesET (P : Parameters)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (test : P.experiment.AdmissibleRule Seed)
    (hfinite : P.bayesExpectedSamples ν test ≠ ⊤) :
    P.experiment.bayesObservationCharge ν test = ENNReal.ofReal P.a * P.expectedPosteriorInformation ν test :=
  P.bayesObservationCharge_eq_posteriorInformation ν test ((P.bayesExpectedSamples_ne_top_iff ν test).mp hfinite)

theorem bayesObservationCharge_eq_posteriorInformation_of_finite_charge (P : Parameters)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (test : P.experiment.AdmissibleRule Seed)
    (hfinite : P.experiment.bayesObservationCharge ν test ≠ ⊤) :
    P.experiment.bayesObservationCharge ν test = ENNReal.ofReal P.a * P.expectedPosteriorInformation ν test := by
  have ho : P.experiment.bayesObjective ν test 0 ≠ ⊤ := by
    simpa only [BinaryExperiment.bayesObjective, zero_mul, add_zero] using hfinite
  exact P.bayesObservationCharge_eq_posteriorInformation ν test
    (P.experiment.bayesObjective_finite_expectedSamples ν test 0 ho)

theorem gatedObservationCharge_eq_posteriorInformation_of_finite_bayesET (P : Parameters)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (test : P.experiment.AdmissibleRule Seed)
    (seeds : Set Seed) (hs : MeasurableSet seeds)
    (hfinite : P.gatedBayesExpectedSamples ν test seeds ≠ ⊤) :
    P.gatedObservationCharge ν test seeds = ENNReal.ofReal P.a * P.gatedPosteriorInformation ν test seeds :=
  P.gatedObservationCharge_eq_posteriorInformation ν test seeds hs
    ((P.gatedBayesExpectedSamples_ne_top_iff ν test seeds).mp hfinite)

end Seed

/-- C03/D03's proved full information interface, for arbitrary private-seed universe,
randomized stopping and arbitrary output decisions. Both conditional finite
ETs are equivalent to finite fair-Bayes ET; no test class is restricted. -/
def StoppedPosteriorInformationIdentity (P : Parameters) : Prop :=
  ∀ (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ test : P.experiment.AdmissibleRule Seed,
        (∀ x, P.experiment.expectedSamples ν test x ≠ ⊤) →
        P.experiment.bayesObservationCharge ν test =
          ENNReal.ofReal P.a * P.expectedPosteriorInformation ν test

theorem stoppedPosteriorInformationIdentity (P : Parameters) : P.StoppedPosteriorInformationIdentity.{u} := by
  intro Seed m ν hν test hfinite
  exact P.bayesObservationCharge_eq_posteriorInformation ν test hfinite

/-- The unnormalized pre-birth restriction, also valid for a zero-mass gate.
Generated earlier history can be included in the independent seed. No event
depending on the current truth, current tape or eventual success is allowed. -/
def PreBirthStoppedPosteriorInformationIdentity (P : Parameters) : Prop :=
  ∀ (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed), MeasurableSet seeds →
        (∀ x, P.gatedExpectedSamples ν test seeds x ≠ ⊤) →
          P.gatedObservationCharge ν test seeds =
            ENNReal.ofReal P.a * P.gatedPosteriorInformation ν test seeds

theorem preBirthStoppedPosteriorInformationIdentity (P : Parameters) :
    P.PreBirthStoppedPosteriorInformationIdentity.{u} := by
  intro Seed m ν hν test seeds hs hfinite
  exact P.gatedObservationCharge_eq_posteriorInformation ν test seeds hs hfinite

/-- The actual BSC increment is bounded by h. The generic library interface
uses a sum over alphabet symbols, which would give the weaker bound 2h. -/
theorem abs_logIncrement_eq_h (P : Parameters) (y : Fin 2) :
    |Real.log (P.experiment.channelReal true y / P.experiment.channelReal false y)| = P.h := by
  rw [P.logIncrement_eq_signed]
  split_ifs <;> simp [abs_of_pos P.h_pos]

theorem bscThreshold_nonneg (p : ℚ) (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hhR : (p : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hhalf
    norm_num at h
    exact h
  exact Real.log_nonneg ((le_div_iff₀ hpR).mpr (by linarith))

/-- A true first boundary crossing overshoots by only one actual BSC step. -/
theorem bscSPRT_score_at_stop_le (P : Parameters) (p : ℚ) (hp : 0 < p) (hhalf : p ≤ 1 / 2)
    (tape : P.experiment.Tape) (n : ℕ) (hs : P.experiment.posteriorThresholdStop p tape = n) :
    |P.experiment.logOddsScore tape n| ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ)) + P.h := by
  cases n with
  | zero =>
    have hz : P.experiment.logOddsScore tape 0 = 0 := by
      rw [P.experiment.logOddsScore_zero]
      norm_num [BinaryExperiment.priorReal, P.prior_eq_half]
    rw [hz, abs_zero]
    exact add_nonneg (bscThreshold_nonneg p hp hhalf) P.h_pos.le
  | succ n =>
    have hb : (n : ℕ∞) < P.experiment.posteriorThresholdStop p tape := by
      rw [hs]
      exact_mod_cast Nat.lt_succ_self n
    have hbefore := P.experiment.logOddsScore_before_stop p tape n hb
    have hi : |Real.log (P.experiment.channelReal true (tape n) /
        P.experiment.channelReal false (tape n))| = P.h := P.abs_logIncrement_eq_h (tape n)
    rw [P.experiment.logOddsScore_succ]
    exact (abs_add_le _ _).trans (by rw [hi]; linarith)

/-- C06's sharp actual conditional charge bound, for the original target
interval 0<p<=1/2. The expectation is finite before any real conversion. -/
theorem bscSPRT_expectedObservationCharge_le (P : Parameters) (p : ℚ)
    (hp : 0 < p) (hhalf : p ≤ 1 / 2) (x : Bool) :
    P.experiment.expectedObservationCharge (Measure.dirac ()) (P.experiment.posteriorSPRT p) x ≤
      ENNReal.ofReal (P.a * (Real.log (1 / (p : ℝ)) + P.h)) := by
  have ha := bscThreshold_nonneg p hp hhalf
  have hfinite := P.experiment.posteriorSPRT_expectedSamples_finite p ha x
  have hcharge := P.experiment.posteriorSPRT_expectedObservationCharge_finite p ha x
  have hplt : p < 1 := by linarith
  have hbound : ∀ᵐ sample ∂(P.experiment.conditionalLaw (Measure.dirac ()) x),
      P.experiment.wordLogLikelihood x
        (P.experiment.stoppedTranscript (P.experiment.posteriorSPRT p) sample).2 ≤
          Real.log (1 / (p : ℝ)) + P.h := by
    filter_upwards [P.experiment.expectedSamples_finite_stop (Measure.dirac ())
      (P.experiment.posteriorSPRT p) x hfinite] with sample hs
    have hstop : P.experiment.posteriorThresholdStop p sample.2 =
        (P.experiment.posteriorThresholdStop p sample.2).toNat := (ENat.natCast_toNat hs).symm
    have hsbound := P.bscSPRT_score_at_stop_le p hp hhalf sample.2 _ hstop
    have hlog := BinaryExperiment.posteriorThreshold_le_log_inv p hp hplt
    have hscore := P.experiment.stoppedWordScore_transcript p sample
    rw [P.stoppedWordScore_eq_wordLogLikelihood] at hscore
    cases x with
    | false =>
      rw [P.wordLogLikelihood_false_eq_neg_true, hscore]
      exact (neg_le_abs _).trans (by linarith)
    | true =>
      rw [hscore]
      exact (le_abs_self _).trans (by linarith)
  have hmean : P.kappa *
      (P.experiment.expectedSamples (Measure.dirac ()) (P.experiment.posteriorSPRT p) x).toReal ≤
        Real.log (1 / (p : ℝ)) + P.h := by
    rw [← P.divergence_eq_kappa x, ← P.experiment.integral_stoppedSum_wald (Measure.dirac ())
      (P.experiment.posteriorSPRT p) x hfinite]
    have hmono := integral_mono_ae
      (P.experiment.integrable_wordLogLikelihood_comp_transcript (Measure.dirac ())
        (P.experiment.posteriorSPRT p) x hfinite)
      (integrable_const (Real.log (1 / (p : ℝ)) + P.h)) hbound
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hmono
  have hreal : (P.experiment.expectedObservationCharge (Measure.dirac ())
      (P.experiment.posteriorSPRT p) x).toReal ≤ P.a * (Real.log (1 / (p : ℝ)) + P.h) := by
    rw [P.experiment.expectedObservationCharge_eq, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal P.experiment.observationFee_real_pos.le]
    calc
      _ ≤ (P.reviewFee : ℝ) * ((Real.log (1 / (p : ℝ)) + P.h) / P.kappa) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ P.kappa_pos).mpr (by simpa only [mul_comm] using hmean))
          (by exact_mod_cast P.reviewFee_pos.le)
      _ = _ := by unfold a; ring
  rw [← ENNReal.ofReal_toReal hcharge]
  exact ENNReal.ofReal_le_ofReal hreal

theorem bscSPRT_bayesObservationCharge_le (P : Parameters) (p : ℚ)
    (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    P.experiment.bayesObservationCharge (Measure.dirac ()) (P.experiment.posteriorSPRT p) ≤
      ENNReal.ofReal (P.a * (Real.log (1 / (p : ℝ)) + P.h)) := by
  unfold BinaryExperiment.bayesObservationCharge
  calc
    _ ≤ ∑ x : Bool, P.experiment.priorMass x *
        ENNReal.ofReal (P.a * (Real.log (1 / (p : ℝ)) + P.h)) :=
      Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (P.bscSPRT_expectedObservationCharge_le p hp hhalf x)
    _ = _ := by rw [← Finset.sum_mul, P.experiment.priorMass_sum, one_mul]

end Parameters
end PaperProofs.Statistics.BinarySymmetric
