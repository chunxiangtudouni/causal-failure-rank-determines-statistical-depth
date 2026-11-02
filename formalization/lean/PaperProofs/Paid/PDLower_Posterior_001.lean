module

public import PaperProofs.Statistics.BSCStoppedPosterior

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Statistics

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem ennreal_ofReal_half : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The actual finite stopped sublaw. Infinite stopping contributes no fake
empty transcript. No finite-expectation or almost-sure-return premise. -/
noncomputable def finiteTranscriptLaw (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) : Measure (Seed × E.StoppedWord) :=
  ((E.conditionalLaw ν x).restrict {sample | test.rule.stop sample.1 sample.2 ≠ ⊤}).map
    (E.stoppedTranscript test)

theorem finiteTranscriptLaw_rectangle (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) (seeds : Set Seed) (hs : MeasurableSet seeds)
    (word : E.StoppedWord) :
    finiteTranscriptLaw E ν test x (seeds ×ˢ {word}) =
      ν (seeds ∩ E.stoppingSeeds test word) * ENNReal.ofReal (E.wordProbability x word) := by
  have hm := hs.prod (measurableSet_singleton word)
  rw [finiteTranscriptLaw, Measure.map_apply (E.measurable_stoppedTranscript test) hm,
    Measure.restrict_apply (hm.preimage (E.measurable_stoppedTranscript test))]
  have heq : (E.stoppedTranscript test) ⁻¹' (seeds ×ˢ {word}) ∩
      {sample | test.rule.stop sample.1 sample.2 ≠ ⊤} =
      (seeds ∩ E.stoppingSeeds test word) ×ˢ E.prefixEvent word := by
    ext sample
    constructor
    · rintro ⟨⟨hseed, hword⟩, hfinite⟩
      have hcast := ENat.natCast_toNat hfinite
      have hlength : (test.rule.stop sample.1 sample.2).toNat = word.1 ↔
          test.rule.stop sample.1 sample.2 = word.1 := by
        rw [← hcast]
        exact ENat.natCast_inj.symm
      have hw : (⟨(test.rule.stop sample.1 sample.2).toNat, fun k => sample.2 k.val⟩ : E.StoppedWord) = word := hword
      obtain ⟨hlen, hpref⟩ := (E.stoppedWord_eq_iff test sample word.1 word.2).mp hw
      have hstop := hlength.mp hlen
      exact ⟨⟨hseed, (E.stop_eq_iff_on_prefix test sample.1 sample.2 word hpref).mp hstop⟩, hpref⟩
    · rintro ⟨⟨hseed, hstop⟩, hpref⟩
      have hstop' := (E.stop_eq_iff_on_prefix test sample.1 sample.2 word hpref).mpr hstop
      refine ⟨⟨hseed, ?_⟩, ?_⟩
      · exact (E.stoppedWord_eq_iff test sample word.1 word.2).mpr ⟨by rw [hstop']; simp, hpref⟩
      · change test.rule.stop sample.1 sample.2 ≠ ⊤
        rw [hstop']
        exact ENat.natCast_ne_top _
  rw [heq]
  change ν.prod (E.tapeLaw x) _ = _
  rw [Measure.prod_prod, E.tapeLaw_prefixEvent]

noncomputable def finiteBayesStoppedLaw (P : BinarySymmetric.Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) : Measure (Seed × P.experiment.StoppedWord) :=
  (1 / 2 : ℝ≥0∞) • finiteTranscriptLaw P.experiment ν test false +
    (1 / 2 : ℝ≥0∞) • finiteTranscriptLaw P.experiment ν test true

theorem finiteBayesStoppedLaw_rectangle (P : BinarySymmetric.Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed) (hs : MeasurableSet seeds)
    (word : P.experiment.StoppedWord) :
    finiteBayesStoppedLaw P ν test (seeds ×ˢ {word}) =
      ν (seeds ∩ P.experiment.stoppingSeeds test word) * ENNReal.ofReal (P.wordEvidence word / 2) := by
  rw [finiteBayesStoppedLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    finiteTranscriptLaw_rectangle P.experiment ν test false seeds hs word,
    finiteTranscriptLaw_rectangle P.experiment ν test true seeds hs word]
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := ennreal_ofReal_half.symm
  have hadd : (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (P.experiment.wordProbability false word) +
      (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (P.experiment.wordProbability true word) =
      ENNReal.ofReal (P.wordEvidence word / 2) := by
    rw [hhalf, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_add
        (mul_nonneg (by norm_num) (P.experiment.wordProbability_pos false word).le)
        (mul_nonneg (by norm_num) (P.experiment.wordProbability_pos true word).le)]
    congr 1
    unfold BinarySymmetric.Parameters.wordEvidence
    ring
  calc
    _ = ν (seeds ∩ P.experiment.stoppingSeeds test word) *
        ((1 / 2 : ℝ≥0∞) * ENNReal.ofReal (P.experiment.wordProbability false word) +
          (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (P.experiment.wordProbability true word)) := by
      simp only [smul_eq_mul]
      ring
    _ = _ := by rw [hadd]

theorem finitePosterior_rectangle (P : BinarySymmetric.Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (seeds : Set Seed) (hs : MeasurableSet seeds)
    (word : P.experiment.StoppedWord) (x : Bool) :
    ENNReal.ofReal (P.wordPosteriorMass x word) * finiteBayesStoppedLaw P ν test (seeds ×ˢ {word}) =
      (1 / 2 : ℝ≥0∞) * finiteTranscriptLaw P.experiment ν test x (seeds ×ˢ {word}) := by
  rw [finiteBayesStoppedLaw_rectangle P ν test seeds hs word,
    finiteTranscriptLaw_rectangle P.experiment ν test x seeds hs word]
  have hreal : P.wordPosteriorMass x word * (P.wordEvidence word / 2) =
      (1 / 2 : ℝ) * P.experiment.wordProbability x word := by
    unfold BinarySymmetric.Parameters.wordPosteriorMass
    field_simp [(P.wordEvidence_pos word).ne']
  calc
    _ = ν (seeds ∩ P.experiment.stoppingSeeds test word) *
        ENNReal.ofReal (P.wordPosteriorMass x word * (P.wordEvidence word / 2)) := by
      rw [ENNReal.ofReal_mul (P.wordPosteriorMass_pos x word).le]
      ring
    _ = _ := by
      rw [hreal, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), ennreal_ofReal_half]
      ring

theorem finiteBayesStoppedLaw_posterior_withDensity (P : BinarySymmetric.Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (x : Bool) :
    (finiteBayesStoppedLaw P ν test).withDensity
      (fun record => ENNReal.ofReal (P.wordPosteriorMass x record.2)) =
      (1 / 2 : ℝ≥0∞) • finiteTranscriptLaw P.experiment ν test x := by
  symm
  apply Measure.ext
  intro B hB
  let sectionAt : P.experiment.StoppedWord → Set Seed := fun word => {seed | (seed, word) ∈ B}
  have hsection (word : P.experiment.StoppedWord) : MeasurableSet (sectionAt word) :=
    hB.preimage (measurable_id.prodMk measurable_const)
  have hset : B = ⋃ word : P.experiment.StoppedWord, sectionAt word ×ˢ {word} := by
    ext record
    simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro hr
      exact ⟨record.2, hr, rfl⟩
    · rintro ⟨word, hs', hw'⟩
      have heq : (record.1, word) = record := Prod.ext rfl hw'.symm
      exact heq ▸ hs'
  have hdisj : Pairwise (fun word word' : P.experiment.StoppedWord => Disjoint
      (sectionAt word ×ˢ {word}) (sectionAt word' ×ˢ {word'})) := by
    intro word word' hne
    apply Set.disjoint_left.mpr
    intro record hr hr'
    exact hne (hr.2.symm.trans hr'.2)
  have hm (word : P.experiment.StoppedWord) : MeasurableSet (sectionAt word ×ˢ {word}) :=
    (hsection word).prod (measurableSet_singleton word)
  rw [hset, measure_iUnion hdisj hm, measure_iUnion hdisj hm]
  apply tsum_congr
  intro word
  rw [Measure.smul_apply, withDensity_apply _ (hm word)]
  have hconstant : ∫⁻ record in sectionAt word ×ˢ {word}, ENNReal.ofReal (P.wordPosteriorMass x record.2)
      ∂(finiteBayesStoppedLaw P ν test) =
      ENNReal.ofReal (P.wordPosteriorMass x word) * finiteBayesStoppedLaw P ν test (sectionAt word ×ˢ {word}) := by
    calc
      _ = ∫⁻ _record in sectionAt word ×ˢ {word}, ENNReal.ofReal (P.wordPosteriorMass x word)
          ∂(finiteBayesStoppedLaw P ν test) := by
        apply setLIntegral_congr_fun (hm word)
        intro record hr
        change ENNReal.ofReal (P.wordPosteriorMass x record.2) = ENNReal.ofReal (P.wordPosteriorMass x word)
        rw [hr.2]
      _ = _ := by simp
  rw [hconstant]
  exact (finitePosterior_rectangle P ν test (sectionAt word) (hsection word) word x).symm

end PDLower
