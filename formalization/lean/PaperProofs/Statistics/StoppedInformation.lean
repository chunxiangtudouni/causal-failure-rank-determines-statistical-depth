module

public import PaperProofs.Statistics.ChannelKL
public import PaperProofs.Statistics.StoppedDecision
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Actual stopped likelihood and information integrability. No stopped likelihood
identity, Wald identity, or independence at a stopping boundary is assumed.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace PaperProofs.Statistics.BinaryExperiment

def wordProbability (E : BinaryExperiment) (x : Bool) (word : E.StoppedWord) : ℝ :=
  ∏ k : Fin word.1, E.channelReal x (word.2 k)

noncomputable def wordLikelihood (E : BinaryExperiment) (x : Bool) (word : E.StoppedWord) : ℝ :=
  ∏ k : Fin word.1, E.channelReal x (word.2 k) / E.channelReal (!x) (word.2 k)

noncomputable def wordLogLikelihood (E : BinaryExperiment) (x : Bool) (word : E.StoppedWord) : ℝ :=
  ∑ k : Fin word.1, Real.log (E.channelReal x (word.2 k) / E.channelReal (!x) (word.2 k))

theorem wordProbability_pos (E : BinaryExperiment) (x : Bool) (word : E.StoppedWord) :
    0 < E.wordProbability x word :=
  Finset.prod_pos fun k _ => E.channelReal_pos x (word.2 k)

theorem wordLikelihood_pos (E : BinaryExperiment) (x : Bool) (word : E.StoppedWord) :
    0 < E.wordLikelihood x word :=
  Finset.prod_pos fun k _ => div_pos (E.channelReal_pos x (word.2 k)) (E.channelReal_pos (!x) (word.2 k))

theorem wordLikelihood_eq_div (E : BinaryExperiment) (x : Bool) (word : E.StoppedWord) :
    E.wordLikelihood x word = E.wordProbability x word / E.wordProbability (!x) word := by
  unfold wordLikelihood wordProbability
  rw [Finset.prod_div_distrib]

theorem wordLikelihood_mul_probability (E : BinaryExperiment) (x : Bool) (word : E.StoppedWord) :
    E.wordLikelihood x word * E.wordProbability (!x) word = E.wordProbability x word := by
  rw [E.wordLikelihood_eq_div]
  exact div_mul_cancel₀ _ (ne_of_gt (E.wordProbability_pos (!x) word))

theorem log_wordLikelihood (E : BinaryExperiment) (x : Bool) (word : E.StoppedWord) :
    Real.log (E.wordLikelihood x word) = E.wordLogLikelihood x word := by
  exact Real.log_prod (fun k _ => ne_of_gt
    (div_pos (E.channelReal_pos x (word.2 k)) (E.channelReal_pos (!x) (word.2 k))))

def prefixEvent (E : BinaryExperiment) (word : E.StoppedWord) : Set E.Tape :=
  {tape | ∀ k : Fin word.1, tape k.val = word.2 k}

theorem measurableSet_prefixEvent (E : BinaryExperiment) (word : E.StoppedWord) :
    MeasurableSet (E.prefixEvent word) := by
  have heq : E.prefixEvent word = ⋂ k : Fin word.1, {tape : E.Tape | tape k.val = word.2 k} := by
    ext tape; simp [prefixEvent]
  rw [heq]
  exact MeasurableSet.iInter fun k => (measurableSet_singleton (word.2 k)).preimage (measurable_pi_apply k.val)

theorem prefixEvent_eq_pi (E : BinaryExperiment) (word : E.StoppedWord) :
    E.prefixEvent word = Set.pi (Finset.range word.1)
      (fun k => {E.completeStoppedWord word k}) := by
  ext tape
  constructor
  · intro h k hk
    have hk' : k < word.1 := Finset.mem_range.mp hk
    simpa only [Set.mem_singleton_iff, completeStoppedWord, hk', ↓reduceDIte] using h ⟨k, hk'⟩
  · intro h k
    have hk := h k.val (Finset.mem_range.mpr k.isLt)
    simpa only [Set.mem_singleton_iff, completeStoppedWord, k.isLt, ↓reduceDIte] using hk

/-- The real infinite iid tape law assigns each finite observed word its actual
finite product mass. Full support gives strictly positive mass for every word. -/
theorem tapeLaw_prefixEvent (E : BinaryExperiment) (x : Bool) (word : E.StoppedWord) :
    E.tapeLaw x (E.prefixEvent word) = ENNReal.ofReal (E.wordProbability x word) := by
  rw [E.prefixEvent_eq_pi]
  change Measure.infinitePi (fun _ : ℕ => E.channelLaw x) _ = _
  rw [Measure.infinitePi_pi _ (fun k _ => measurableSet_singleton _)]
  simp_rw [E.channelLaw_singleton]
  rw [← Fin.prod_univ_eq_prod_range]
  have heq (k : Fin word.1) : E.completeStoppedWord word k.val = word.2 k :=
    E.completeStoppedWord_prefix word.1 word.2 k.val k.isLt
  simp_rw [heq]
  symm
  exact ENNReal.ofReal_prod_of_nonneg (fun k _ => (E.channelReal_pos x (word.2 k)).le)

theorem tapeLaw_prefixEvent_pos (E : BinaryExperiment) (x : Bool) (word : E.StoppedWord) :
    0 < E.tapeLaw x (E.prefixEvent word) := by
  rw [E.tapeLaw_prefixEvent]
  exact ENNReal.ofReal_pos.mpr (E.wordProbability_pos x word)

noncomputable def logIncrementBound (E : BinaryExperiment) (x : Bool) : ℝ :=
  ∑ y : Fin E.alphabetSize, |Real.log (E.channelReal x y / E.channelReal (!x) y)|

theorem logIncrementBound_nonneg (E : BinaryExperiment) (x : Bool) : 0 ≤ E.logIncrementBound x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem logIncrement_norm_le (E : BinaryExperiment) (x : Bool) (y : Fin E.alphabetSize) :
    ‖Real.log (E.channelReal x y / E.channelReal (!x) y)‖ ≤ E.logIncrementBound x := by
  change |Real.log (E.channelReal x y / E.channelReal (!x) y)| ≤ E.logIncrementBound x
  exact Finset.single_le_sum (fun z _ => abs_nonneg
    (Real.log (E.channelReal x z / E.channelReal (!x) z))) (Finset.mem_univ y)

theorem wordLogLikelihood_norm_le (E : BinaryExperiment) (x : Bool) (word : E.StoppedWord) :
    ‖E.wordLogLikelihood x word‖ ≤ E.logIncrementBound x * word.1 := by
  calc
    _ ≤ ∑ k : Fin word.1, ‖Real.log (E.channelReal x (word.2 k) / E.channelReal (!x) (word.2 k))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k : Fin word.1, E.logIncrementBound x :=
      Finset.sum_le_sum fun k _ => E.logIncrement_norm_le x (word.2 k)
    _ = _ := by simp [mul_comm]

section PrivateSeed

variable {Seed : Type*} [MeasurableSpace Seed]

def stoppingSeeds (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (word : E.StoppedWord) : Set Seed :=
  {seed | test.rule.stop seed (E.completeStoppedWord word) = word.1}

theorem measurableSet_stoppingSeeds (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (word : E.StoppedWord) : MeasurableSet (E.stoppingSeeds test word) :=
  (measurableSet_singleton (word.1 : ℕ∞)).preimage
    (test.measurable_stop.comp (measurable_id.prodMk measurable_const))

theorem stop_eq_iff_on_prefix (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (seed : Seed) (tape : E.Tape) (word : E.StoppedWord) (hprefix : tape ∈ E.prefixEvent word) :
    test.rule.stop seed tape = word.1 ↔ seed ∈ E.stoppingSeeds test word := by
  have hp : ∀ k < word.1, tape k = E.completeStoppedWord word k := by
    intro k hk
    rw [E.completeStoppedWord_prefix word.1 word.2 k hk]
    exact hprefix ⟨k, hk⟩
  constructor
  · intro hs
    exact E.stopping_preserved_by_prefix test.rule seed tape (E.completeStoppedWord word) word.1 hs hp
  · intro hs
    exact E.stopping_preserved_by_prefix test.rule seed (E.completeStoppedWord word) tape word.1 hs
      (fun k hk => (hp k hk).symm)

/-- The causal stop event has one common private-seed gate in both truth laws.
This is a consequence of the actual stopping-rule field, not a likelihood premise. -/
theorem finiteStoppedEvent_eq_rectangle (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (word : E.StoppedWord) :
    {sample : Seed × E.Tape | test.rule.stop sample.1 sample.2 = word.1 ∧ sample.2 ∈ E.prefixEvent word} =
      E.stoppingSeeds test word ×ˢ E.prefixEvent word := by
  ext sample
  constructor
  · rintro ⟨hs, hp⟩
    exact ⟨(E.stop_eq_iff_on_prefix test sample.1 sample.2 word hp).mp hs, hp⟩
  · rintro ⟨hs, hp⟩
    exact ⟨(E.stop_eq_iff_on_prefix test sample.1 sample.2 word hp).mpr hs, hp⟩

theorem stoppedTranscript_rectangle_ae (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) (hfinite : E.expectedSamples ν test x ≠ ⊤)
    (seeds : Set Seed) (word : E.StoppedWord) :
    (E.stoppedTranscript test) ⁻¹' (seeds ×ˢ {word}) =ᵐ[E.conditionalLaw ν x]
      ((seeds ∩ E.stoppingSeeds test word) ×ˢ E.prefixEvent word) := by
  filter_upwards [E.expectedSamples_finite_stop ν test x hfinite] with sample hsample
  have hcast := ENat.natCast_toNat hsample
  have hlength : (test.rule.stop sample.1 sample.2).toNat = word.1 ↔
      test.rule.stop sample.1 sample.2 = word.1 := by
    rw [← hcast]
    exact ENat.natCast_inj.symm
  apply propext
  change (sample.1 ∈ seeds ∧
      (⟨(test.rule.stop sample.1 sample.2).toNat, fun k => sample.2 k.val⟩ : E.StoppedWord) = word) ↔
    (sample.1 ∈ seeds ∧ sample.1 ∈ E.stoppingSeeds test word) ∧ sample.2 ∈ E.prefixEvent word
  rw [E.stoppedWord_eq_iff test sample word.1 word.2, hlength]
  constructor
  · rintro ⟨hs, hstop, hp⟩
    exact ⟨⟨hs, (E.stop_eq_iff_on_prefix test sample.1 sample.2 word hp).mp hstop⟩, hp⟩
  · rintro ⟨⟨hs, hstop⟩, hp⟩
    exact ⟨hs, (E.stop_eq_iff_on_prefix test sample.1 sample.2 word hp).mpr hstop, hp⟩

/-- Actual stopped-transcript mass on every private-seed by word rectangle.
The finite-ET hypothesis is used solely to remove the genuine infinity event. -/
theorem transcriptLaw_rectangle_singleton (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) (hfinite : E.expectedSamples ν test x ≠ ⊤)
    (seeds : Set Seed) (hseeds : MeasurableSet seeds) (word : E.StoppedWord) :
    E.transcriptLaw ν test x (seeds ×ˢ {word}) =
      ν (seeds ∩ E.stoppingSeeds test word) * ENNReal.ofReal (E.wordProbability x word) := by
  rw [E.transcriptLaw_apply ν test x _ (hseeds.prod (measurableSet_singleton word)),
    measure_congr (E.stoppedTranscript_rectangle_ae ν test x hfinite seeds word)]
  change ν.prod (E.tapeLaw x) _ = _
  rw [Measure.prod_prod, E.tapeLaw_prefixEvent]

noncomputable def transcriptLikelihood (E : BinaryExperiment) (x : Bool)
    (record : Seed × E.StoppedWord) : ℝ≥0∞ :=
  ENNReal.ofReal (E.wordLikelihood x record.2)

theorem measurable_transcriptLikelihood (E : BinaryExperiment) (x : Bool) :
    Measurable (E.transcriptLikelihood (Seed := Seed) x) :=
  (measurable_of_countable (fun word : E.StoppedWord => ENNReal.ofReal (E.wordLikelihood x word))).comp measurable_snd

theorem transcriptLaw_withDensity_rectangle (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool)
    (hfinite : ∀ x, E.expectedSamples ν test x ≠ ⊤)
    (seeds : Set Seed) (hseeds : MeasurableSet seeds) (word : E.StoppedWord) :
    E.transcriptLaw ν test x (seeds ×ˢ {word}) =
      ((E.transcriptLaw ν test (!x)).withDensity (E.transcriptLikelihood x)) (seeds ×ˢ {word}) := by
  rw [withDensity_apply _ (hseeds.prod (measurableSet_singleton word))]
  have heq : ∫⁻ record in seeds ×ˢ {word}, E.transcriptLikelihood x record ∂(E.transcriptLaw ν test (!x)) =
      ENNReal.ofReal (E.wordLikelihood x word) * E.transcriptLaw ν test (!x) (seeds ×ˢ {word}) := by
    calc
      _ = ∫⁻ _record in seeds ×ˢ {word}, ENNReal.ofReal (E.wordLikelihood x word)
          ∂(E.transcriptLaw ν test (!x)) := by
        apply setLIntegral_congr_fun (hseeds.prod (measurableSet_singleton word))
        intro record hrecord
        have hw : record.2 = word := hrecord.2
        simp only [transcriptLikelihood, hw]
      _ = _ := by simp
  rw [heq, E.transcriptLaw_rectangle_singleton ν test x (hfinite x) seeds hseeds word,
    E.transcriptLaw_rectangle_singleton ν test (!x) (hfinite (!x)) seeds hseeds word]
  rw [mul_left_comm, ← ENNReal.ofReal_mul (E.wordLikelihood_pos x word).le,
    E.wordLikelihood_mul_probability]

/-- The actual stopped-transcript density. This is proved on finite-word
rectangles, then extended over their countable disjoint union. It never asserts
absolute continuity of the full infinite tapes. -/
theorem transcriptLaw_withDensity (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool)
    (hfinite : ∀ x, E.expectedSamples ν test x ≠ ⊤) :
    E.transcriptLaw ν test x =
      (E.transcriptLaw ν test (!x)).withDensity (E.transcriptLikelihood x) := by
  apply Measure.ext_prod
  intro seeds words hseeds _hwords
  have hset : seeds ×ˢ words = ⋃ word : words, seeds ×ˢ {word.val} := by
    ext record
    simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hs, hw⟩
      exact ⟨⟨record.2, hw⟩, hs, rfl⟩
    · rintro ⟨word, hs, hw⟩
      exact ⟨hs, hw ▸ word.property⟩
  have hdisj : Pairwise (fun word word' : words => Disjoint (seeds ×ˢ {word.val}) (seeds ×ˢ {word'.val})) := by
    intro word word' hne
    apply Set.disjoint_left.mpr
    intro record hr hr'
    apply hne
    apply Subtype.ext
    exact hr.2.symm.trans hr'.2
  have hm (word : words) : MeasurableSet (seeds ×ˢ {word.val}) :=
    hseeds.prod (measurableSet_singleton word.val)
  rw [hset, measure_iUnion hdisj hm, measure_iUnion hdisj hm]
  apply tsum_congr
  intro word
  exact E.transcriptLaw_withDensity_rectangle ν test x hfinite seeds hseeds word.val

theorem transcriptLaw_absolutelyContinuous (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool)
    (hfinite : ∀ x, E.expectedSamples ν test x ≠ ⊤) :
    E.transcriptLaw ν test x ≪ E.transcriptLaw ν test (!x) := by
  rw [E.transcriptLaw_withDensity ν test x hfinite]
  exact withDensity_absolutelyContinuous _ _

theorem transcriptLaw_rnDeriv (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool)
    (hfinite : ∀ x, E.expectedSamples ν test x ≠ ⊤) :
    (E.transcriptLaw ν test x).rnDeriv (E.transcriptLaw ν test (!x)) =ᵐ[E.transcriptLaw ν test (!x)]
      E.transcriptLikelihood x := by
  nth_rw 1 [E.transcriptLaw_withDensity ν test x hfinite]
  exact Measure.rnDeriv_withDensity _ (E.measurable_transcriptLikelihood x)

/-- True stopped likelihood is the sum of the actually observed log increments. -/
theorem transcriptLaw_llr (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool)
    (hfinite : ∀ x, E.expectedSamples ν test x ≠ ⊤) :
    llr (E.transcriptLaw ν test x) (E.transcriptLaw ν test (!x)) =ᵐ[E.transcriptLaw ν test x]
      (fun record => E.wordLogLikelihood x record.2) := by
  have h := (E.transcriptLaw_absolutelyContinuous ν test x hfinite).ae_eq
    (E.transcriptLaw_rnDeriv ν test x hfinite)
  filter_upwards [h] with record hrecord
  rw [llr, hrecord, transcriptLikelihood,
    ENNReal.toReal_ofReal (E.wordLikelihood_pos x record.2).le, E.log_wordLikelihood]

theorem integrable_wordLogLikelihood_comp_transcript (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) (hfinite : E.expectedSamples ν test x ≠ ⊤) :
    Integrable (fun sample => E.wordLogLikelihood x (E.stoppedTranscript test sample).2)
      (E.conditionalLaw ν x) := by
  have hm : Measurable (fun sample => E.wordLogLikelihood x (E.stoppedTranscript test sample).2) :=
    (measurable_of_countable (E.wordLogLikelihood x)).comp
      (E.measurable_stoppedTranscript test).snd
  apply ((E.expectedSamples_finite_integrable_toNat ν test x hfinite).const_mul
    (E.logIncrementBound x)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun sample => E.wordLogLikelihood_norm_le x (E.stoppedTranscript test sample).2)

theorem integrable_wordLogLikelihood_transcriptLaw (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) (hfinite : E.expectedSamples ν test x ≠ ⊤) :
    Integrable (fun record : Seed × E.StoppedWord => E.wordLogLikelihood x record.2)
      (E.transcriptLaw ν test x) := by
  have hm : Measurable (fun record : Seed × E.StoppedWord => E.wordLogLikelihood x record.2) :=
    (measurable_of_countable (E.wordLogLikelihood x)).comp measurable_snd
  exact (integrable_map_measure hm.aestronglyMeasurable (E.measurable_stoppedTranscript test).aemeasurable).mpr
    (E.integrable_wordLogLikelihood_comp_transcript ν test x hfinite)

theorem integrable_transcriptLaw_llr (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool)
    (hfinite : ∀ x, E.expectedSamples ν test x ≠ ⊤) :
    Integrable (llr (E.transcriptLaw ν test x) (E.transcriptLaw ν test (!x)))
      (E.transcriptLaw ν test x) :=
  (E.integrable_wordLogLikelihood_transcriptLaw ν test x (hfinite x)).congr
    (E.transcriptLaw_llr ν test x hfinite).symm

/-- Information is the mean actual stopped sum. StoppedWald proves its mean
from predictable increments; all RN/absolute-continuity/integrability steps here are proved. -/
theorem transcriptLaw_klDiv_eq_ofReal_stoppedSum (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool)
    (hfinite : ∀ x, E.expectedSamples ν test x ≠ ⊤) :
    InformationTheory.klDiv (E.transcriptLaw ν test x) (E.transcriptLaw ν test (!x)) =
      ENNReal.ofReal (∫ sample, E.wordLogLikelihood x (E.stoppedTranscript test sample).2
        ∂(E.conditionalLaw ν x)) := by
  rw [InformationTheory.klDiv_of_ac_of_integrable
    (E.transcriptLaw_absolutelyContinuous ν test x hfinite)
    (E.integrable_transcriptLaw_llr ν test x hfinite)]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, add_sub_cancel_right]
  rw [integral_congr_ae (E.transcriptLaw_llr ν test x hfinite)]
  congr 1
  exact integral_map (E.measurable_stoppedTranscript test).aemeasurable
    (((measurable_of_countable (E.wordLogLikelihood x)).comp measurable_snd).aestronglyMeasurable)

end PrivateSeed

end PaperProofs.Statistics.BinaryExperiment
