module

public import PaperProofs.Statistics.StoppedInformation

/-!
Wald's identity for the actual iid channel, arbitrary independent private seed,
and causal test. Survival is proved to be a function of the seed and previous
observations. Finite truncated sums have the exact drift identity; finite
extended ET then supplies an integrable dominating bound for the limit.

Together with the separately proved stopped-transcript density, this closes
`StoppedInformationIdentity` and its decision-information consequence.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace PaperProofs.Statistics.BinaryExperiment

abbrev PrefixTape (E : BinaryExperiment) (n : ℕ) :=
  {k : ℕ // k < n} → Fin E.alphabetSize

def prefixView (E : BinaryExperiment) {Seed : Type*} (n : ℕ)
    (sample : Seed × E.Tape) : Seed × E.PrefixTape n :=
  (sample.1, fun k => sample.2 k.val)

theorem tapePrefix_independent_next (E : BinaryExperiment) (x : Bool) (n : ℕ) :
    IndepFun (fun tape : E.Tape => fun k : {k : ℕ // k < n} => tape k.val)
      (fun tape => tape n) (E.tapeLaw x) := by
  have hdisj : Disjoint {k : ℕ | k < n} {n} :=
    Set.disjoint_singleton_right.mpr (Nat.lt_irrefl n)
  have h := (E.tapeLaw_independent x).indepFun_set {k : ℕ | k < n} {n} hdisj
    (fun k => measurable_pi_apply k)
  exact h.comp measurable_id (measurable_pi_apply (⟨n, Set.mem_singleton n⟩ : ({n} : Set ℕ)))

noncomputable def completePrefixTape (E : BinaryExperiment) (n : ℕ)
    (past : E.PrefixTape n) : E.Tape :=
  fun k => if hk : k < n then past ⟨k, hk⟩ else E.completionSymbol

theorem measurable_completePrefixTape (E : BinaryExperiment) (n : ℕ) :
    Measurable (E.completePrefixTape n) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : k < n
  · simpa only [completePrefixTape, hk, ↓reduceDIte] using
      (measurable_pi_apply (⟨k, hk⟩ : {k : ℕ // k < n}))
  · simpa only [completePrefixTape, hk, ↓reduceDIte] using
      (measurable_const : Measurable (fun _ : E.PrefixTape n => E.completionSymbol))

section PrivateSeed

variable {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_prefixView (E : BinaryExperiment) (n : ℕ) :
    Measurable (E.prefixView (Seed := Seed) n) :=
  measurable_fst.prodMk (measurable_pi_iff.mpr fun k => (measurable_pi_apply k.val).comp measurable_snd)

theorem conditionalLaw_tapeCoordinate (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (x : Bool) (n : ℕ) :
    (E.conditionalLaw ν x).map (fun sample => sample.2 n) = E.channelLaw x := by
  calc
    _ = ((E.conditionalLaw ν x).map Prod.snd).map (fun tape => tape n) :=
      (Measure.map_map (measurable_pi_apply n) measurable_snd).symm
    _ = (E.tapeLaw x).map (fun tape => tape n) := by simp [conditionalLaw]
    _ = _ := E.tapeLaw_coordinate x n

theorem conditionalLaw_prefixView (E : BinaryExperiment) (ν : Measure Seed) (x : Bool) (n : ℕ) :
    (E.conditionalLaw ν x).map (E.prefixView n) =
      ν.prod ((E.tapeLaw x).map (fun tape => fun k : {k : ℕ // k < n} => tape k.val)) := by
  have hp : Measurable (fun tape : E.Tape => fun k : {k : ℕ // k < n} => tape k.val) :=
    measurable_pi_iff.mpr fun k => measurable_pi_apply k.val
  have heq : Prod.map (id : Seed → Seed)
      (fun tape : E.Tape => fun k : {k : ℕ // k < n} => tape k.val) = E.prefixView n := by
    funext sample
    rcases sample with ⟨seed, tape⟩
    rfl
  unfold conditionalLaw
  rw [← heq]
  simpa only [Measure.map_id] using (Measure.map_prod_map ν (E.tapeLaw x) measurable_id hp).symm

theorem prefixView_independent_next (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (x : Bool) (n : ℕ) :
    IndepFun (E.prefixView (Seed := Seed) n) (fun sample : Seed × E.Tape => sample.2 n)
      (E.conditionalLaw ν x) := by
  let past : E.Tape → E.PrefixTape n := fun tape k => tape k.val
  have hp : Measurable past := measurable_pi_iff.mpr fun k => measurable_pi_apply k.val
  have hn : Measurable (fun tape : E.Tape => tape n) := measurable_pi_apply n
  have hnext : Measurable (fun sample : Seed × E.Tape => sample.2 n) := hn.comp measurable_snd
  have hjoint : (E.tapeLaw x).map (fun tape => (past tape, tape n)) =
      ((E.tapeLaw x).map past).prod (E.channelLaw x) := by
    rw [(E.tapePrefix_independent_next x n).map_prod_eq_prod_map_map hp.aemeasurable hn.aemeasurable,
      E.tapeLaw_coordinate]
  have hseeded : (E.conditionalLaw ν x).map
      (fun sample => (sample.1, (past sample.2, sample.2 n))) =
      ν.prod (((E.tapeLaw x).map past).prod (E.channelLaw x)) := by
    calc
      _ = ν.prod ((E.tapeLaw x).map (fun tape => (past tape, tape n))) := by
        have heq : Prod.map (id : Seed → Seed) (fun tape : E.Tape => (past tape, tape n)) =
            (fun sample : Seed × E.Tape => (sample.1, (past sample.2, sample.2 n))) := by
          funext sample
          rcases sample with ⟨seed, tape⟩
          rfl
        unfold conditionalLaw
        rw [← heq]
        simpa only [Measure.map_id] using
          (Measure.map_prod_map ν (E.tapeLaw x) measurable_id (hp.prodMk hn)).symm
      _ = _ := by rw [hjoint]
  apply (indepFun_iff_map_prod_eq_prod_map_map (E.measurable_prefixView n).aemeasurable hnext.aemeasurable).mpr
  rw [E.conditionalLaw_prefixView, E.conditionalLaw_tapeCoordinate]
  apply (MeasurableEquiv.prodAssoc :
    (Seed × E.PrefixTape n) × Fin E.alphabetSize ≃ᵐ Seed × E.PrefixTape n × Fin E.alphabetSize).map_measurableEquiv_injective
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable
    ((E.measurable_prefixView n).prodMk hnext), Measure.prodAssoc_prod]
  exact hseeded

noncomputable def continueIndicator (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (n : ℕ) (sample : Seed × E.Tape) : ℝ :=
  if (n : ℕ∞) < test.rule.stop sample.1 sample.2 then 1 else 0

noncomputable def continueFromPrefix (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (n : ℕ) (record : Seed × E.PrefixTape n) : ℝ :=
  if (n : ℕ∞) < test.rule.stop record.1 (E.completePrefixTape n record.2) then 1 else 0

theorem measurable_continueIndicator (E : BinaryExperiment) (test : E.AdmissibleRule Seed) (n : ℕ) :
    Measurable (E.continueIndicator test n) := by
  exact measurable_const.ite ((Set.to_countable (Set.Ioi (n : ℕ∞))).measurableSet.preimage test.measurable_stop) measurable_const

theorem measurable_continueFromPrefix (E : BinaryExperiment) (test : E.AdmissibleRule Seed) (n : ℕ) :
    Measurable (E.continueFromPrefix test n) := by
  apply measurable_const.ite _ measurable_const
  exact (Set.to_countable (Set.Ioi (n : ℕ∞))).measurableSet.preimage (test.measurable_stop.comp
    (measurable_fst.prodMk ((E.measurable_completePrefixTape n).comp measurable_snd)))

theorem continueFromPrefix_eq (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (n : ℕ) (sample : Seed × E.Tape) :
    E.continueFromPrefix test n (E.prefixView n sample) = E.continueIndicator test n sample := by
  have hp : ∀ k < n, sample.2 k = E.completePrefixTape n (fun k => sample.2 k.val) k := by
    intro k hk
    simp only [completePrefixTape, hk, ↓reduceDIte]
  have h := test.rule.stopping sample.1 sample.2 (E.completePrefixTape n (fun k => sample.2 k.val)) n hp
  have hlt : (n : ℕ∞) < test.rule.stop sample.1 sample.2 ↔
      (n : ℕ∞) < test.rule.stop sample.1 (E.completePrefixTape n (fun k => sample.2 k.val)) := by
    simpa only [not_le] using not_congr h
  simp only [continueFromPrefix, prefixView, continueIndicator, hlt]
  rfl

theorem continueIndicator_independent_next (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool) (n : ℕ) :
    IndepFun (E.continueIndicator test n) (fun sample : Seed × E.Tape => sample.2 n)
      (E.conditionalLaw ν x) := by
  have heq : E.continueIndicator test n = fun sample => E.continueFromPrefix test n (E.prefixView n sample) :=
    funext fun sample => (E.continueFromPrefix_eq test n sample).symm
  rw [heq]
  exact (E.prefixView_independent_next ν x n).comp (E.measurable_continueFromPrefix test n) measurable_id

noncomputable def logIncrement (E : BinaryExperiment) (x : Bool) (n : ℕ)
    (sample : Seed × E.Tape) : ℝ :=
  Real.log (E.channelReal x (sample.2 n) / E.channelReal (!x) (sample.2 n))

theorem measurable_logIncrement (E : BinaryExperiment) (x : Bool) (n : ℕ) :
    Measurable (E.logIncrement (Seed := Seed) x n) :=
  (measurable_of_countable (fun y => Real.log (E.channelReal x y / E.channelReal (!x) y))).comp
    ((measurable_pi_apply n).comp measurable_snd)

theorem integral_logIncrement (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (x : Bool) (n : ℕ) :
    ∫ sample, E.logIncrement x n sample ∂(E.conditionalLaw ν x) = E.divergence x := by
  have hm : Measurable (fun y : Fin E.alphabetSize => Real.log (E.channelReal x y / E.channelReal (!x) y)) :=
    measurable_of_countable _
  have hmap := integral_map ((measurable_pi_apply n).comp measurable_snd).aemeasurable
    hm.aestronglyMeasurable (μ := E.conditionalLaw ν x)
  simp only [Function.comp_def] at hmap
  rw [E.conditionalLaw_tapeCoordinate] at hmap
  unfold logIncrement
  rw [← hmap]
  simpa only [E.channelLaw_llr] using E.channelLaw_integral_llr x

theorem integrable_continueIndicator (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool) (n : ℕ) :
    Integrable (E.continueIndicator test n) (E.conditionalLaw ν x) := by
  apply (integrable_const (1 : ℝ)).mono' (E.measurable_continueIndicator test n).aestronglyMeasurable
  apply ae_of_all
  intro sample
  simp only [continueIndicator]
  split_ifs <;> norm_num

theorem integrable_stoppedIncrement (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool) (n : ℕ) :
    Integrable (fun sample => E.continueIndicator test n sample * E.logIncrement x n sample)
      (E.conditionalLaw ν x) := by
  apply (integrable_const (E.logIncrementBound x)).mono'
    ((E.measurable_continueIndicator test n).mul (E.measurable_logIncrement x n)).aestronglyMeasurable
  apply ae_of_all
  intro sample
  by_cases hstop : (n : ℕ∞) < test.rule.stop sample.1 sample.2
  · simpa only [Pi.mul_apply, continueIndicator, hstop, ↓reduceIte, one_mul, logIncrement]
      using E.logIncrement_norm_le x (sample.2 n)
  · simpa only [Pi.mul_apply, continueIndicator, hstop, ↓reduceIte, zero_mul, norm_zero]
      using E.logIncrementBound_nonneg x

theorem integral_stoppedIncrement (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool) (n : ℕ) :
    ∫ sample, E.continueIndicator test n sample * E.logIncrement x n sample ∂(E.conditionalLaw ν x) =
      E.divergence x * ∫ sample, E.continueIndicator test n sample ∂(E.conditionalLaw ν x) := by
  have hind := (E.continueIndicator_independent_next ν test x n).comp measurable_id
    (measurable_of_countable (fun y => Real.log (E.channelReal x y / E.channelReal (!x) y)))
  have hi := hind.integral_mul_eq_mul_integral
    (E.measurable_continueIndicator test n).aestronglyMeasurable (E.measurable_logIncrement x n).aestronglyMeasurable
  change (∫ sample, E.continueIndicator test n sample * E.logIncrement x n sample ∂(E.conditionalLaw ν x)) =
    (∫ sample, E.continueIndicator test n sample ∂(E.conditionalLaw ν x)) *
      (∫ sample, E.logIncrement x n sample ∂(E.conditionalLaw ν x)) at hi
  rw [E.integral_logIncrement] at hi
  simpa only [Pi.mul_apply, mul_comm] using hi

noncomputable def truncatedStoppedSum (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (x : Bool) (N : ℕ) (sample : Seed × E.Tape) : ℝ :=
  ∑ n ∈ Finset.range N, E.continueIndicator test n sample * E.logIncrement x n sample

noncomputable def truncatedCount (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (N : ℕ) (sample : Seed × E.Tape) : ℝ :=
  ∑ n ∈ Finset.range N, E.continueIndicator test n sample

theorem integral_truncatedStoppedSum (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool) (N : ℕ) :
    ∫ sample, E.truncatedStoppedSum test x N sample ∂(E.conditionalLaw ν x) =
      E.divergence x * ∫ sample, E.truncatedCount test N sample ∂(E.conditionalLaw ν x) := by
  unfold truncatedStoppedSum truncatedCount
  rw [integral_finsetSum _ (fun n _ => E.integrable_stoppedIncrement ν test x n),
    integral_finsetSum _ (fun n _ => E.integrable_continueIndicator ν test x n)]
  simp_rw [E.integral_stoppedIncrement]
  exact (Finset.mul_sum _ _ _).symm

theorem continueIndicator_eq_of_finite (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (sample : Seed × E.Tape) (hfinite : test.rule.stop sample.1 sample.2 ≠ ⊤) (n : ℕ) :
    E.continueIndicator test n sample = if n < (test.rule.stop sample.1 sample.2).toNat then 1 else 0 := by
  have hcast := ENat.natCast_toNat hfinite
  have hiff : (n : ℕ∞) < test.rule.stop sample.1 sample.2 ↔ n < (test.rule.stop sample.1 sample.2).toNat := by
    rw [← hcast]
    exact ENat.natCast_lt_natCast
  simp only [continueIndicator, hiff]

theorem truncatedCount_eq_of_finite (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (N : ℕ) (sample : Seed × E.Tape) (hfinite : test.rule.stop sample.1 sample.2 ≠ ⊤) :
    E.truncatedCount test N sample = (min N (test.rule.stop sample.1 sample.2).toNat : ℕ) := by
  unfold truncatedCount
  simp_rw [E.continueIndicator_eq_of_finite test sample hfinite]
  rw [Finset.sum_boole]
  have heq : (Finset.range N).filter (fun n => n < (test.rule.stop sample.1 sample.2).toNat) =
      Finset.range (min N (test.rule.stop sample.1 sample.2).toNat) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  rw [heq, Finset.card_range]

theorem truncatedStoppedSum_eq_of_finite (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (x : Bool) (N : ℕ) (sample : Seed × E.Tape) (hfinite : test.rule.stop sample.1 sample.2 ≠ ⊤) :
    E.truncatedStoppedSum test x N sample =
      ∑ n ∈ Finset.range (min N (test.rule.stop sample.1 sample.2).toNat), E.logIncrement x n sample := by
  unfold truncatedStoppedSum
  simp_rw [E.continueIndicator_eq_of_finite test sample hfinite, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]

theorem measurable_truncatedStoppedSum (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (x : Bool) (N : ℕ) : Measurable (E.truncatedStoppedSum test x N) :=
  Finset.measurable_sum _ (fun n _ =>
    (E.measurable_continueIndicator test n).mul (E.measurable_logIncrement x n))

theorem measurable_truncatedCount (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (N : ℕ) : Measurable (E.truncatedCount test N) :=
  Finset.measurable_sum _ (fun n _ => E.measurable_continueIndicator test n)

theorem truncatedCount_norm_le (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (N : ℕ) (sample : Seed × E.Tape) (hfinite : test.rule.stop sample.1 sample.2 ≠ ⊤) :
    ‖E.truncatedCount test N sample‖ ≤ ((test.rule.stop sample.1 sample.2).toNat : ℝ) := by
  rw [E.truncatedCount_eq_of_finite test N sample hfinite, Real.norm_natCast]
  exact_mod_cast min_le_right N (test.rule.stop sample.1 sample.2).toNat

theorem truncatedStoppedSum_norm_le (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (x : Bool) (N : ℕ) (sample : Seed × E.Tape) (hfinite : test.rule.stop sample.1 sample.2 ≠ ⊤) :
    ‖E.truncatedStoppedSum test x N sample‖ ≤
      E.logIncrementBound x * (test.rule.stop sample.1 sample.2).toNat := by
  rw [E.truncatedStoppedSum_eq_of_finite test x N sample hfinite]
  calc
    _ ≤ ∑ n ∈ Finset.range (min N (test.rule.stop sample.1 sample.2).toNat), ‖E.logIncrement x n sample‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range (min N (test.rule.stop sample.1 sample.2).toNat), E.logIncrementBound x :=
      Finset.sum_le_sum fun n _ => E.logIncrement_norm_le x (sample.2 n)
    _ = E.logIncrementBound x * (min N (test.rule.stop sample.1 sample.2).toNat : ℕ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right N (test.rule.stop sample.1 sample.2).toNat)
      (E.logIncrementBound_nonneg x)

theorem truncatedCount_eventually_eq (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (sample : Seed × E.Tape) (hfinite : test.rule.stop sample.1 sample.2 ≠ ⊤) :
    ∀ᶠ N : ℕ in Filter.atTop, E.truncatedCount test N sample = (test.rule.stop sample.1 sample.2).toNat := by
  filter_upwards [Filter.eventually_ge_atTop (test.rule.stop sample.1 sample.2).toNat] with N hN
  rw [E.truncatedCount_eq_of_finite test N sample hfinite, min_eq_right hN]

theorem truncatedStoppedSum_eventually_eq (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (x : Bool) (sample : Seed × E.Tape) (hfinite : test.rule.stop sample.1 sample.2 ≠ ⊤) :
    ∀ᶠ N : ℕ in Filter.atTop, E.truncatedStoppedSum test x N sample =
      E.wordLogLikelihood x (E.stoppedTranscript test sample).2 := by
  filter_upwards [Filter.eventually_ge_atTop (test.rule.stop sample.1 sample.2).toNat] with N hN
  rw [E.truncatedStoppedSum_eq_of_finite test x N sample hfinite, min_eq_right hN]
  symm
  exact Fin.sum_univ_eq_sum_range
    (fun n => Real.log (E.channelReal x (sample.2 n) / E.channelReal (!x) (sample.2 n))) _

/-- Wald's identity for this actual arbitrary privately randomized causal test.
Finite extended ET supplies both the a.e. finite stopping count and the
integrable dominating bound; no optional-stopping conclusion is assumed. -/
theorem integral_stoppedSum_wald (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool)
    (hfinite : E.expectedSamples ν test x ≠ ⊤) :
    (∫ sample, E.wordLogLikelihood x (E.stoppedTranscript test sample).2 ∂(E.conditionalLaw ν x)) =
      E.divergence x * (E.expectedSamples ν test x).toReal := by
  have hcount := tendsto_integral_of_dominated_convergence
    (f := fun sample : Seed × E.Tape => ((test.rule.stop sample.1 sample.2).toNat : ℝ))
    (fun sample : Seed × E.Tape => ((test.rule.stop sample.1 sample.2).toNat : ℝ))
    (fun N => (E.measurable_truncatedCount test N).aestronglyMeasurable)
    (E.expectedSamples_finite_integrable_toNat ν test x hfinite)
    (fun N => by
      filter_upwards [E.expectedSamples_finite_stop ν test x hfinite] with sample hs
      exact E.truncatedCount_norm_le test N sample hs)
    (by
      filter_upwards [E.expectedSamples_finite_stop ν test x hfinite] with sample hs
      exact Filter.Tendsto.congr'
        (Filter.Eventually.mono (E.truncatedCount_eventually_eq test sample hs) (fun _ hN => hN.symm))
        tendsto_const_nhds)
  have hsum := tendsto_integral_of_dominated_convergence
    (f := fun sample : Seed × E.Tape => E.wordLogLikelihood x (E.stoppedTranscript test sample).2)
    (fun sample : Seed × E.Tape => E.logIncrementBound x * ((test.rule.stop sample.1 sample.2).toNat : ℝ))
    (fun N => (E.measurable_truncatedStoppedSum test x N).aestronglyMeasurable)
    ((E.expectedSamples_finite_integrable_toNat ν test x hfinite).const_mul (E.logIncrementBound x))
    (fun N => by
      filter_upwards [E.expectedSamples_finite_stop ν test x hfinite] with sample hs
      exact E.truncatedStoppedSum_norm_le test x N sample hs)
    (by
      filter_upwards [E.expectedSamples_finite_stop ν test x hfinite] with sample hs
      exact Filter.Tendsto.congr'
        (Filter.Eventually.mono (E.truncatedStoppedSum_eventually_eq test x sample hs) (fun _ hN => hN.symm))
        tendsto_const_nhds)
  have hcount' := hcount.const_mul (E.divergence x)
  simp_rw [← E.integral_truncatedStoppedSum ν test x] at hcount'
  have heq := tendsto_nhds_unique hsum hcount'
  rw [E.expectedSamples_finite_integral_toNat ν test x hfinite] at heq
  exact heq

theorem stoppedInformationIdentity (E : BinaryExperiment) : E.StoppedInformationIdentity := by
  intro Seed m
  let : MeasurableSpace Seed := m
  intro ν hν test hfinite
  let : IsProbabilityMeasure ν := hν
  refine ⟨E.measurable_stoppedTranscript test, ?_⟩
  intro x
  rw [E.transcriptLaw_klDiv_eq_ofReal_stoppedSum ν test x hfinite,
    E.integral_stoppedSum_wald ν test x (hfinite x),
    ENNReal.ofReal_mul (E.divergence_pos x).le]
  congr 1
  exact ENNReal.ofReal_toReal (hfinite x)

end PrivateSeed

theorem stoppedDecisionInformationBound (E : BinaryExperiment) : E.StoppedDecisionInformationBound :=
  E.stoppedDecisionInformationBound_of_identity E.stoppedInformationIdentity

end PaperProofs.Statistics.BinaryExperiment
