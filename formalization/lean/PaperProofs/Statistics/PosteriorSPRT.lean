module

public import PaperProofs.Statistics.StoppedWald

/-!
The original posterior-threshold SPRT, with its actual first exit and MAP
decision. Finite extended ET follows from finite truncated Wald and bounded
overshoot. The Bayes error follows from the actual stopped-record density
and a pointwise posterior-odds inequality. No test guarantee is assumed.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace PaperProofs.Statistics.BinaryExperiment

theorem logOddsScore_eq_of_prefix (E : BinaryExperiment) (tape tape' : E.Tape) (n : ℕ)
    (hprefix : ∀ k < n, tape k = tape' k) : E.logOddsScore tape n = E.logOddsScore tape' n := by
  unfold logOddsScore
  congr 1
  exact Finset.sum_congr rfl (fun k hk => by rw [hprefix k (Finset.mem_range.mp hk)])

theorem measurable_logOddsScore (E : BinaryExperiment) (n : ℕ) :
    Measurable (fun tape => E.logOddsScore tape n) := by
  unfold logOddsScore
  apply measurable_const.add
  exact Finset.measurable_sum _ (fun k _ =>
    (measurable_of_countable (fun y => Real.log (E.channelReal true y / E.channelReal false y))).comp
      (measurable_pi_apply k))

theorem posteriorThresholdStop_le_iff (E : BinaryExperiment) (p : ℚ) (tape : E.Tape) (n : ℕ) :
    E.posteriorThresholdStop p tape ≤ n ↔ ∃ k ≤ n,
      Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤ |E.logOddsScore tape k| := by
  classical
  let hits : Set ℕ∞ := {t | ∃ k : ℕ, t = k ∧
    Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤ |E.logOddsScore tape k|}
  change sInf hits ≤ (n : ℕ∞) ↔ _
  constructor
  · intro hs
    have hnonempty : hits.Nonempty := by
      by_contra h
      have hempty : hits = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [hempty, sInf_empty] at hs
      exact ENat.top_ne_natCast n (top_le_iff.mp hs).symm
    obtain ⟨k, hk, hh⟩ := csInf_mem hnonempty
    refine ⟨k, ?_, hh⟩
    rw [hk] at hs
    exact ENat.natCast_le_natCast.mp hs
  · rintro ⟨k, hkn, hh⟩
    exact (sInf_le (show (k : ℕ∞) ∈ hits from ⟨k, rfl, hh⟩)).trans (by exact_mod_cast hkn)

theorem posteriorThresholdStop_stopping (E : BinaryExperiment) (p : ℚ) :
    E.IsStoppingRule (fun _seed : Unit => E.posteriorThresholdStop p) := by
  intro _seed tape tape' n hp
  rw [E.posteriorThresholdStop_le_iff, E.posteriorThresholdStop_le_iff]
  constructor <;> rintro ⟨k, hkn, hh⟩ <;> refine ⟨k, hkn, ?_⟩
  · rwa [← E.logOddsScore_eq_of_prefix tape tape' k (fun j hj => hp j (hj.trans_le hkn))]
  · rwa [E.logOddsScore_eq_of_prefix tape tape' k (fun j hj => hp j (hj.trans_le hkn))]

theorem measurable_posteriorThresholdStop (E : BinaryExperiment) (p : ℚ) :
    Measurable (E.posteriorThresholdStop p) := by
  apply ENat.measurable_iff.mpr
  intro n
  have hm (m : ℕ) : MeasurableSet {tape : E.Tape | E.posteriorThresholdStop p tape ≤ m} := by
    have hset : {tape : E.Tape | E.posteriorThresholdStop p tape ≤ m} =
        ⋃ k : Fin (m + 1), {tape | Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤ |E.logOddsScore tape k.val|} := by
      ext tape
      simp only [Set.mem_ofPred_eq, E.posteriorThresholdStop_le_iff, Set.mem_iUnion]
      constructor
      · rintro ⟨k, hk, hh⟩
        exact ⟨⟨k, Nat.lt_succ_iff.mpr hk⟩, hh⟩
      · rintro ⟨k, hh⟩
        exact ⟨k.val, Nat.lt_succ_iff.mp k.isLt, hh⟩
    rw [hset]
    exact MeasurableSet.iUnion fun k => by
      simpa only [Real.norm_eq_abs] using measurableSet_le measurable_const (E.measurable_logOddsScore k.val).norm
  cases n with
  | zero =>
    have heq : (E.posteriorThresholdStop p) ⁻¹' {(0 : ℕ∞)} =
        {tape : E.Tape | E.posteriorThresholdStop p tape ≤ 0} := by
      ext tape; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, nonpos_iff_eq_zero]
    simpa only [Nat.cast_zero, heq] using hm 0
  | succ n =>
    have heq : (E.posteriorThresholdStop p) ⁻¹' {(n + 1 : ℕ∞)} =
        {tape : E.Tape | E.posteriorThresholdStop p tape ≤ n + 1} \
          {tape : E.Tape | E.posteriorThresholdStop p tape ≤ n} := by
      ext tape
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
      constructor
      · intro h
        rw [h]
        exact ⟨le_rfl, not_le.mpr (by exact_mod_cast Nat.lt_succ_self n)⟩
      · rintro ⟨hle, hnot⟩
        apply le_antisymm hle
        exact ENat.natCast_add_one_le_iff.mpr (lt_of_not_ge hnot)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [heq]
    exact (hm (n + 1)).diff (hm n)

noncomputable def posteriorSPRT (E : BinaryExperiment) (p : ℚ) : E.AdmissibleRule Unit where
  rule := {
    stop := fun _ tape => E.posteriorThresholdStop p tape
    decision := fun _ tape => decide (0 ≤ E.logOddsScore tape (E.posteriorThresholdStop p tape).toNat)
    stopping := E.posteriorThresholdStop_stopping p
    stoppedDecision := by
      intro _seed tape tape' n hs hs' hp
      simp only [hs, hs', ENat.toNat_natCast]
      rw [E.logOddsScore_eq_of_prefix tape tape' n hp]
  }
  measurable_stop := (E.measurable_posteriorThresholdStop p).comp measurable_snd
  measurable_decision := by
    have hn : Measurable (fun sample : Unit × E.Tape => (E.posteriorThresholdStop p sample.2).toNat) :=
      (measurable_of_countable ENat.toNat).comp ((E.measurable_posteriorThresholdStop p).comp measurable_snd)
    have hjoint : Measurable (fun pair : E.Tape × ℕ => E.logOddsScore pair.1 pair.2) :=
      measurable_from_prod_countable_left (fun n => E.measurable_logOddsScore n)
    have hscore := hjoint.comp (measurable_snd.prodMk hn)
    apply measurable_to_bool
    simpa only [Function.comp_def, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
      (measurableSet_le measurable_const hscore)

theorem posteriorSPRT_isPosteriorThresholdRule (E : BinaryExperiment) (p : ℚ) :
    E.IsPosteriorThresholdRule p (E.posteriorSPRT p) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro tape n hn
  change decide (0 ≤ E.logOddsScore tape (E.posteriorThresholdStop p tape).toNat) = _
  change E.posteriorThresholdStop p tape = n at hn
  simp only [hn, ENat.toNat_natCast]

theorem logOddsScore_zero (E : BinaryExperiment) (tape : E.Tape) :
    E.logOddsScore tape 0 = Real.log (E.priorReal true / E.priorReal false) := by
  simp [logOddsScore]

theorem logOddsScore_succ (E : BinaryExperiment) (tape : E.Tape) (n : ℕ) :
    E.logOddsScore tape (n + 1) = E.logOddsScore tape n +
      Real.log (E.channelReal true (tape n) / E.channelReal false (tape n)) := by
  simp only [logOddsScore, Finset.sum_range_succ]
  ring

theorem posteriorThresholdStop_hits (E : BinaryExperiment) (p : ℚ) (tape : E.Tape) (n : ℕ)
    (hstop : E.posteriorThresholdStop p tape = n) :
    Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤ |E.logOddsScore tape n| := by
  obtain ⟨k, hkn, hk⟩ := (E.posteriorThresholdStop_le_iff p tape n).mp (by rw [hstop])
  have hnk : n ≤ k := by
    have hle := (E.posteriorThresholdStop_le_iff p tape k).mpr ⟨k, le_rfl, hk⟩
    rw [hstop] at hle
    exact ENat.natCast_le_natCast.mp hle
  have heq := Nat.le_antisymm hkn hnk
  simpa only [heq] using hk

theorem logOddsScore_before_stop (E : BinaryExperiment) (p : ℚ) (tape : E.Tape) (n : ℕ)
    (hbefore : (n : ℕ∞) < E.posteriorThresholdStop p tape) :
    |E.logOddsScore tape n| < Real.log ((1 - (p : ℝ)) / (p : ℝ)) := by
  apply lt_of_not_ge
  intro hhit
  exact (not_le_of_gt hbefore) ((E.posteriorThresholdStop_le_iff p tape n).mpr ⟨n, le_rfl, hhit⟩)

/-- At a genuine finite first exit, only one bounded observation increment
can cross the boundary. A clock-zero exit keeps the original prior score. -/
theorem logOddsScore_at_stop_bound (E : BinaryExperiment) (p : ℚ) (tape : E.Tape)
    (ha : 0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ))) (n : ℕ)
    (hstop : E.posteriorThresholdStop p tape = n) :
    |E.logOddsScore tape n| ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ)) + E.logIncrementBound true +
      |Real.log (E.priorReal true / E.priorReal false)| := by
  cases n with
  | zero =>
    rw [E.logOddsScore_zero]
    have hK := E.logIncrementBound_nonneg true
    linarith
  | succ n =>
    have hb : (n : ℕ∞) < E.posteriorThresholdStop p tape := by
      rw [hstop]
      exact_mod_cast Nat.lt_succ_self n
    have hscore := E.logOddsScore_before_stop p tape n hb
    have hinc := E.logIncrement_norm_le true (tape n)
    rw [Real.norm_eq_abs] at hinc
    change |Real.log (E.channelReal true (tape n) / E.channelReal false (tape n))| ≤ E.logIncrementBound true at hinc
    rw [E.logOddsScore_succ]
    exact (abs_add_le _ _).trans (by have hp := abs_nonneg (Real.log (E.priorReal true / E.priorReal false)); linarith)

theorem logIncrement_false (E : BinaryExperiment) {Seed : Type*} (n : ℕ) (sample : Seed × E.Tape) :
    E.logIncrement false n sample = -E.logIncrement true n sample := by
  simp only [logIncrement, Bool.not_false, Bool.not_true,
    Real.log_div (ne_of_gt (E.channelReal_pos false _)) (ne_of_gt (E.channelReal_pos true _)),
    Real.log_div (ne_of_gt (E.channelReal_pos true _)) (ne_of_gt (E.channelReal_pos false _))]
  ring

theorem prefixLogSum_norm_le_score (E : BinaryExperiment) {Seed : Type*} (sample : Seed × E.Tape)
    (x : Bool) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, E.logIncrement x k sample‖ ≤
      |E.logOddsScore sample.2 n| + |Real.log (E.priorReal true / E.priorReal false)| := by
  have htrue : ∑ k ∈ Finset.range n, E.logIncrement true k sample =
      E.logOddsScore sample.2 n - Real.log (E.priorReal true / E.priorReal false) := by
    simp only [logOddsScore, logIncrement, Bool.not_true]
    ring
  have hb : |E.logOddsScore sample.2 n - Real.log (E.priorReal true / E.priorReal false)| ≤
      |E.logOddsScore sample.2 n| + |Real.log (E.priorReal true / E.priorReal false)| := abs_sub _ _
  cases x with
  | true => simpa only [htrue, Real.norm_eq_abs] using hb
  | false =>
    simp_rw [E.logIncrement_false, Finset.sum_neg_distrib]
    simpa only [norm_neg, htrue, Real.norm_eq_abs] using hb

noncomputable def sprtSumBound (E : BinaryExperiment) (p : ℚ) : ℝ :=
  Real.log ((1 - (p : ℝ)) / (p : ℝ)) + E.logIncrementBound true +
    2 * |Real.log (E.priorReal true / E.priorReal false)|

theorem sprtSumBound_nonneg (E : BinaryExperiment) (p : ℚ)
    (ha : 0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ))) : 0 ≤ E.sprtSumBound p := by
  unfold sprtSumBound
  have hK := E.logIncrementBound_nonneg true
  have hc := abs_nonneg (Real.log (E.priorReal true / E.priorReal false))
  linarith

theorem posteriorSPRT_truncatedSum_bound (E : BinaryExperiment) (p : ℚ)
    (ha : 0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ))) (x : Bool) (N : ℕ)
    (sample : Unit × E.Tape) :
    ‖E.truncatedStoppedSum (E.posteriorSPRT p) x N sample‖ ≤ E.sprtSumBound p := by
  by_cases hstop : E.posteriorThresholdStop p sample.2 ≤ N
  · obtain ⟨n, hn, hnN⟩ := ENat.le_natCast_iff.mp hstop
    have hf : (E.posteriorSPRT p).rule.stop sample.1 sample.2 ≠ ⊤ := by
      change E.posteriorThresholdStop p sample.2 ≠ ⊤
      rw [hn]
      exact ENat.natCast_ne_top n
    rw [E.truncatedStoppedSum_eq_of_finite (E.posteriorSPRT p) x N sample hf]
    change ‖∑ k ∈ Finset.range (min N (E.posteriorThresholdStop p sample.2).toNat), E.logIncrement x k sample‖ ≤ _
    rw [hn, ENat.toNat_natCast, min_eq_right hnN]
    have hs := E.logOddsScore_at_stop_bound p sample.2 ha n hn
    have hsum := E.prefixLogSum_norm_le_score sample x n
    unfold sprtSumBound
    linarith
  · have hbefore : (N : ℕ∞) < E.posteriorThresholdStop p sample.2 := lt_of_not_ge hstop
    have hsum : E.truncatedStoppedSum (E.posteriorSPRT p) x N sample =
        ∑ k ∈ Finset.range N, E.logIncrement x k sample := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : (k : ℕ∞) < E.posteriorThresholdStop p sample.2 :=
        (ENat.natCast_lt_natCast.mpr (Finset.mem_range.mp hk)).trans hbefore
      change (if (k : ℕ∞) < E.posteriorThresholdStop p sample.2 then (1 : ℝ) else 0) * _ = _
      simp only [hk', ↓reduceIte, one_mul]
    rw [hsum]
    have hs := E.logOddsScore_before_stop p sample.2 N hbefore
    have hnorm := E.prefixLogSum_norm_le_score sample x N
    have hK := E.logIncrementBound_nonneg true
    have hp := abs_nonneg (Real.log (E.priorReal true / E.priorReal false))
    unfold sprtSumBound
    linarith

section TruncatedExpectation

variable {Seed : Type*} [MeasurableSpace Seed]

theorem truncatedCount_eq_top (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (N : ℕ) (sample : Seed × E.Tape) (htop : test.rule.stop sample.1 sample.2 = ⊤) :
    E.truncatedCount test N sample = N := by
  simp only [truncatedCount, continueIndicator, htop, ENat.natCast_lt_top, ↓reduceIte,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem truncatedCount_nonneg (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (N : ℕ) (sample : Seed × E.Tape) : 0 ≤ E.truncatedCount test N sample := by
  by_cases ht : test.rule.stop sample.1 sample.2 = ⊤
  · rw [E.truncatedCount_eq_top test N sample ht]
    exact Nat.cast_nonneg _
  · rw [E.truncatedCount_eq_of_finite test N sample ht]
    exact Nat.cast_nonneg _

theorem truncatedCount_monotone (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (sample : Seed × E.Tape) : Monotone (fun N => E.truncatedCount test N sample) := by
  intro N M hNM
  change E.truncatedCount test N sample ≤ E.truncatedCount test M sample
  by_cases ht : test.rule.stop sample.1 sample.2 = ⊤
  · rw [E.truncatedCount_eq_top test N sample ht, E.truncatedCount_eq_top test M sample ht]
    exact_mod_cast hNM
  · rw [E.truncatedCount_eq_of_finite test N sample ht, E.truncatedCount_eq_of_finite test M sample ht]
    exact_mod_cast min_le_min_right _ hNM

theorem iSup_ofReal_truncatedCount (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (sample : Seed × E.Tape) :
    (⨆ N : ℕ, ENNReal.ofReal (E.truncatedCount test N sample)) =
      sampleCountENNReal (test.rule.stop sample.1 sample.2) := by
  by_cases ht : test.rule.stop sample.1 sample.2 = ⊤
  · simp_rw [E.truncatedCount_eq_top test _ sample ht, ENNReal.ofReal_natCast]
    rw [ht, sampleCountENNReal_top]
    exact ENNReal.iSup_natCast
  · simp only [sampleCountENNReal, ht, ↓reduceIte]
    apply le_antisymm
    · apply iSup_le
      intro N
      rw [E.truncatedCount_eq_of_finite test N sample ht, ENNReal.ofReal_natCast]
      exact_mod_cast min_le_right N (test.rule.stop sample.1 sample.2).toNat
    · have h := le_iSup (fun N : ℕ => ENNReal.ofReal (E.truncatedCount test N sample))
        (test.rule.stop sample.1 sample.2).toNat
      simpa only [E.truncatedCount_eq_of_finite test _ sample ht, min_self, ENNReal.ofReal_natCast] using h

theorem expectedSamples_eq_iSup_truncatedCount (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool) :
    E.expectedSamples ν test x =
      ⨆ N : ℕ, ENNReal.ofReal (∫ sample, E.truncatedCount test N sample ∂(E.conditionalLaw ν x)) := by
  have heq : (fun sample : Seed × E.Tape => sampleCountENNReal (test.rule.stop sample.1 sample.2)) =
      fun sample => ⨆ N : ℕ, ENNReal.ofReal (E.truncatedCount test N sample) :=
    funext fun sample => (E.iSup_ofReal_truncatedCount test sample).symm
  unfold expectedSamples
  rw [heq, lintegral_iSup]
  · congr 1
    funext N
    symm
    apply ofReal_integral_eq_lintegral_ofReal
    · exact integrable_finsetSum _ (fun n _ => E.integrable_continueIndicator ν test x n)
    · exact ae_of_all _ (E.truncatedCount_nonneg test N)
  · intro N
    exact (E.measurable_truncatedCount test N).ennreal_ofReal
  · intro N M hNM sample
    exact ENNReal.ofReal_le_ofReal (E.truncatedCount_monotone test sample hNM)

end TruncatedExpectation

theorem posteriorSPRT_integral_truncatedCount_le (E : BinaryExperiment) (p : ℚ)
    (ha : 0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ))) (x : Bool) (N : ℕ) :
    (∫ sample, E.truncatedCount (E.posteriorSPRT p) N sample
      ∂(E.conditionalLaw (Measure.dirac ()) x)) ≤ E.sprtSumBound p / E.divergence x := by
  have hi : Integrable (E.truncatedStoppedSum (E.posteriorSPRT p) x N)
      (E.conditionalLaw (Measure.dirac ()) x) :=
    integrable_finsetSum _ (fun n _ => E.integrable_stoppedIncrement (Measure.dirac ()) (E.posteriorSPRT p) x n)
  have hle := integral_mono hi (integrable_const (E.sprtSumBound p))
    (fun sample => (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using E.posteriorSPRT_truncatedSum_bound p ha x N sample))
  rw [E.integral_truncatedStoppedSum] at hle
  have hc : ∫ _sample : Unit × E.Tape, E.sprtSumBound p
      ∂(E.conditionalLaw (Measure.dirac ()) x) = E.sprtSumBound p := by simp
  rw [hc] at hle
  exact (le_div_iff₀ (E.divergence_pos x)).mpr (by simpa only [mul_comm] using hle)

theorem posteriorSPRT_expectedSamples_le (E : BinaryExperiment) (p : ℚ)
    (ha : 0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ))) (x : Bool) :
    E.expectedSamples (Measure.dirac ()) (E.posteriorSPRT p) x ≤
      ENNReal.ofReal (E.sprtSumBound p / E.divergence x) := by
  rw [E.expectedSamples_eq_iSup_truncatedCount]
  exact iSup_le fun N => ENNReal.ofReal_le_ofReal (E.posteriorSPRT_integral_truncatedCount_le p ha x N)

theorem posteriorSPRT_expectedSamples_finite (E : BinaryExperiment) (p : ℚ)
    (ha : 0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ))) (x : Bool) :
    E.expectedSamples (Measure.dirac ()) (E.posteriorSPRT p) x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (E.posteriorSPRT_expectedSamples_le p ha x)

theorem posteriorSPRT_expectedObservationCharge_finite (E : BinaryExperiment) (p : ℚ)
    (ha : 0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ))) (x : Bool) :
    E.expectedObservationCharge (Measure.dirac ()) (E.posteriorSPRT p) x ≠ ⊤ := by
  rw [E.expectedObservationCharge_eq]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (E.posteriorSPRT_expectedSamples_finite p ha x)

theorem posteriorSPRT_expectedObservationCharge_le (E : BinaryExperiment) (p : ℚ)
    (ha : 0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ))) (x : Bool) :
    (E.expectedObservationCharge (Measure.dirac ()) (E.posteriorSPRT p) x).toReal ≤
      (E.observationFee : ℝ) / E.divergence x * E.sprtSumBound p := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (E.posteriorSPRT_expectedSamples_le p ha x)
  rw [ENNReal.toReal_ofReal (div_nonneg (E.sprtSumBound_nonneg p ha) (E.divergence_pos x).le)] at h
  rw [E.expectedObservationCharge_eq, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal E.observationFee_real_pos.le]
  calc
    _ ≤ (E.observationFee : ℝ) * (E.sprtSumBound p / E.divergence x) :=
      mul_le_mul_of_nonneg_left h E.observationFee_real_pos.le
    _ = _ := by ring

theorem posteriorThreshold_nonneg (p : ℚ) (hp : 0 < p) (hpquarter : p ≤ 1 / 4) :
    0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hpRquarter : (p : ℝ) ≤ 1 / 4 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hpquarter
    norm_num at h
    exact h
  apply Real.log_nonneg
  exact (le_div_iff₀ hpR).mpr (by linarith)

theorem posteriorThreshold_le_log_inv (p : ℚ) (hp : 0 < p) (hplt : p < 1) :
    Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤ Real.log (1 / (p : ℝ)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hpltR : (p : ℝ) < 1 := by exact_mod_cast hplt
  apply Real.log_le_log (div_pos (sub_pos.mpr hpltR) hpR)
  exact div_le_div_of_nonneg_right (by linarith) hpR.le

theorem posteriorSPRT_sharpObservationCharge (E : BinaryExperiment) (p : ℚ)
    (hp : 0 < p) (hpquarter : p ≤ 1 / 4) (x : Bool) :
    (E.expectedObservationCharge (Measure.dirac ()) (E.posteriorSPRT p) x).toReal ≤
      (E.observationFee : ℝ) / E.divergence x *
        (Real.log (1 / (p : ℝ)) + (E.logIncrementBound true +
          2 * |Real.log (E.priorReal true / E.priorReal false)|)) := by
  have hplt : p < 1 := by linarith
  apply (E.posteriorSPRT_expectedObservationCharge_le p (posteriorThreshold_nonneg p hp hpquarter) x).trans
  apply mul_le_mul_of_nonneg_left
  · unfold sprtSumBound
    have hlog := posteriorThreshold_le_log_inv p hp hplt
    linarith
  · exact div_nonneg E.observationFee_real_pos.le (E.divergence_pos x).le

noncomputable def stoppedWordScore (E : BinaryExperiment) (word : E.StoppedWord) : ℝ :=
  Real.log (E.priorReal true / E.priorReal false) + E.wordLogLikelihood true word

theorem stoppedWordScore_eq_log_odds (E : BinaryExperiment) (word : E.StoppedWord) :
    E.stoppedWordScore word = Real.log
      (E.priorReal true * E.wordLikelihood true word / E.priorReal false) := by
  rw [stoppedWordScore, ← E.log_wordLikelihood,
    Real.log_div (ne_of_gt (E.priorReal_pos true)) (ne_of_gt (E.priorReal_pos false)),
    Real.log_div (ne_of_gt (mul_pos (E.priorReal_pos true) (E.wordLikelihood_pos true word)))
      (ne_of_gt (E.priorReal_pos false)),
    Real.log_mul (ne_of_gt (E.priorReal_pos true)) (ne_of_gt (E.wordLikelihood_pos true word))]
  ring

theorem stoppedWordScore_transcript (E : BinaryExperiment) (p : ℚ) (sample : Unit × E.Tape) :
    E.stoppedWordScore (E.stoppedTranscript (E.posteriorSPRT p) sample).2 =
      E.logOddsScore sample.2 (E.posteriorThresholdStop p sample.2).toNat := by
  unfold stoppedWordScore wordLogLikelihood stoppedTranscript logOddsScore
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun n => Real.log (E.channelReal true (sample.2 n) / E.channelReal false (sample.2 n))) _

noncomputable def posteriorRecordDecision (E : BinaryExperiment) (record : Unit × E.StoppedWord) : Bool :=
  decide (0 ≤ E.stoppedWordScore record.2)

theorem measurable_stoppedWordScore (E : BinaryExperiment) : Measurable E.stoppedWordScore :=
  measurable_of_countable _

theorem measurable_posteriorRecordDecision (E : BinaryExperiment) : Measurable E.posteriorRecordDecision := by
  apply measurable_to_bool
  simpa only [Function.comp_def, posteriorRecordDecision, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
    (measurableSet_le measurable_const (E.measurable_stoppedWordScore.comp measurable_snd))

theorem posteriorRecordDecision_comp (E : BinaryExperiment) (p : ℚ) (sample : Unit × E.Tape) :
    E.posteriorRecordDecision (E.stoppedTranscript (E.posteriorSPRT p) sample) =
      (E.posteriorSPRT p).rule.decision sample.1 sample.2 := by
  simp only [posteriorRecordDecision, E.stoppedWordScore_transcript]
  rfl

theorem stoppedWordScore_threshold_ae (E : BinaryExperiment) (p : ℚ)
    (ha : 0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ))) :
    ∀ᵐ record ∂(E.transcriptLaw (Measure.dirac ()) (E.posteriorSPRT p) false),
      Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤ |E.stoppedWordScore record.2| := by
  have hm : MeasurableSet {record : Unit × E.StoppedWord |
      Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤ |E.stoppedWordScore record.2|} := by
    simpa only [Function.comp_def, Real.norm_eq_abs] using measurableSet_le measurable_const
      (E.measurable_stoppedWordScore.comp measurable_snd).norm
  apply (ae_map_iff (E.measurable_stoppedTranscript (E.posteriorSPRT p)).aemeasurable hm).mpr
  filter_upwards [E.expectedSamples_finite_stop (Measure.dirac ()) (E.posteriorSPRT p) false
    (E.posteriorSPRT_expectedSamples_finite p ha false)] with sample hs
  rw [E.stoppedWordScore_transcript]
  apply E.posteriorThresholdStop_hits p sample.2 _
  exact (ENat.natCast_toNat hs).symm

theorem posteriorSPRT_conditionalError_transcript (E : BinaryExperiment) (p : ℚ) (x : Bool) :
    E.conditionalError (Measure.dirac ()) (E.posteriorSPRT p) x =
      E.transcriptLaw (Measure.dirac ()) (E.posteriorSPRT p) x {record | E.posteriorRecordDecision record ≠ x} := by
  have hm : MeasurableSet {record | E.posteriorRecordDecision record ≠ x} :=
    ((E.measurable_posteriorRecordDecision) (measurableSet_singleton x)).compl
  rw [E.transcriptLaw_apply _ _ _ _ hm]
  unfold conditionalError
  congr 1
  ext sample
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, E.posteriorRecordDecision_comp]

/-- Deterministic posterior-odds inequality behind Bayes risk ≤ p. -/
theorem posteriorRisk_inequality (a b p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hp : 0 < p) (hpone : p < 1)
    (hthreshold : Real.log ((1 - p) / p) ≤ |Real.log (b / a)|) :
    (if 0 ≤ Real.log (b / a) then a else b) ≤ p * (a + b) := by
  by_cases hs : 0 ≤ Real.log (b / a)
  · rw [ite_eq_left hs]
    rw [abs_of_nonneg hs] at hthreshold
    have hodds := (Real.log_le_log_iff (div_pos (sub_pos.mpr hpone) hp) (div_pos hb ha)).mp hthreshold
    have hmul := (div_le_div_iff₀ hp ha).mp hodds
    nlinarith
  · rw [ite_eq_right hs]
    rw [abs_of_neg (lt_of_not_ge hs)] at hthreshold
    have hneg : -Real.log (b / a) = Real.log (a / b) := by
      rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha), Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
      ring
    rw [hneg] at hthreshold
    have hodds := (Real.log_le_log_iff (div_pos (sub_pos.mpr hpone) hp) (div_pos ha hb)).mp hthreshold
    have hmul := (div_le_div_iff₀ hp hb).mp hodds
    nlinarith

noncomputable def posteriorRecordRisk (E : BinaryExperiment) (record : Unit × E.StoppedWord) : ℝ≥0∞ :=
  if E.posteriorRecordDecision record then E.priorMass false
  else E.priorMass true * E.transcriptLikelihood true record

theorem posteriorRecordRisk_ofReal (E : BinaryExperiment) (record : Unit × E.StoppedWord) :
    E.posteriorRecordRisk record = ENNReal.ofReal
      (if 0 ≤ E.stoppedWordScore record.2 then E.priorReal false
       else E.priorReal true * E.wordLikelihood true record.2) := by
  classical
  by_cases hs : 0 ≤ E.stoppedWordScore record.2
  · simp only [posteriorRecordRisk, posteriorRecordDecision, hs, decide_true, ↓reduceIte, priorMass]
  · simp only [posteriorRecordRisk, posteriorRecordDecision, hs, decide_false, Bool.false_eq_true,
      ↓reduceIte, priorMass, transcriptLikelihood,
      ENNReal.ofReal_mul (E.priorReal_pos true).le]

theorem posteriorRecordRisk_le (E : BinaryExperiment) (p : ℚ) (hp : 0 < p) (hplt : p < 1)
    (record : Unit × E.StoppedWord)
    (hthreshold : Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤ |E.stoppedWordScore record.2|) :
    E.posteriorRecordRisk record ≤ ENNReal.ofReal (p : ℝ) *
      (E.priorMass false + E.priorMass true * E.transcriptLikelihood true record) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hpltR : (p : ℝ) < 1 := by exact_mod_cast hplt
  have hreal := posteriorRisk_inequality (E.priorReal false)
    (E.priorReal true * E.wordLikelihood true record.2) (p : ℝ)
    (E.priorReal_pos false) (mul_pos (E.priorReal_pos true) (E.wordLikelihood_pos true record.2)) hpR hpltR
    (by simpa only [E.stoppedWordScore_eq_log_odds] using hthreshold)
  have htotal : E.priorMass false + E.priorMass true * E.transcriptLikelihood true record =
      ENNReal.ofReal (E.priorReal false + E.priorReal true * E.wordLikelihood true record.2) := by
    rw [ENNReal.ofReal_add (E.priorReal_pos false).le
      (mul_pos (E.priorReal_pos true) (E.wordLikelihood_pos true record.2)).le,
      ENNReal.ofReal_mul (E.priorReal_pos true).le]
    rfl
  rw [E.posteriorRecordRisk_ofReal, htotal, ← ENNReal.ofReal_mul hpR.le]
  apply ENNReal.ofReal_le_ofReal
  simpa only [E.stoppedWordScore_eq_log_odds] using hreal

theorem posteriorRecordRisk_eq_indicators (E : BinaryExperiment) :
    E.posteriorRecordRisk = fun record : Unit × E.StoppedWord =>
      {record | E.posteriorRecordDecision record = true}.indicator (fun _ => E.priorMass false) record +
      {record | E.posteriorRecordDecision record = false}.indicator
        (fun record => E.priorMass true * E.transcriptLikelihood true record) record := by
  funext record
  cases h : E.posteriorRecordDecision record <;> simp [posteriorRecordRisk, h]

theorem bayesError_posteriorSPRT_eq_integral (E : BinaryExperiment) (p : ℚ)
    (ha : 0 ≤ Real.log ((1 - (p : ℝ)) / (p : ℝ))) :
    E.bayesError (Measure.dirac ()) (E.posteriorSPRT p) =
      ∫⁻ record, E.posteriorRecordRisk record
        ∂(E.transcriptLaw (Measure.dirac ()) (E.posteriorSPRT p) false) := by
  let μ := E.transcriptLaw (Measure.dirac ()) (E.posteriorSPRT p) false
  have hfinite : ∀ x, E.expectedSamples (Measure.dirac ()) (E.posteriorSPRT p) x ≠ ⊤ :=
    E.posteriorSPRT_expectedSamples_finite p ha
  have hm (b : Bool) : MeasurableSet {record : Unit × E.StoppedWord | E.posteriorRecordDecision record = b} :=
    (E.measurable_posteriorRecordDecision) (measurableSet_singleton b)
  have htrue : E.transcriptLaw (Measure.dirac ()) (E.posteriorSPRT p) true =
      μ.withDensity (E.transcriptLikelihood true) :=
    E.transcriptLaw_withDensity _ _ true hfinite
  rw [E.posteriorRecordRisk_eq_indicators, lintegral_add_left (measurable_const.indicator (hm true)),
    lintegral_indicator_const (hm true)]
  have hfalseIntegral : ∫⁻ record, {record | E.posteriorRecordDecision record = false}.indicator
        (fun record => E.priorMass true * E.transcriptLikelihood true record) record ∂μ =
      E.priorMass true * E.transcriptLaw (Measure.dirac ()) (E.posteriorSPRT p) true
        {record | E.posteriorRecordDecision record = false} := by
    rw [lintegral_indicator (hm false), htrue,
      withDensity_apply _ (hm false)]
    exact lintegral_const_mul _ (E.measurable_transcriptLikelihood true)
  rw [hfalseIntegral]
  unfold bayesError
  rw [Fintype.sum_bool, E.posteriorSPRT_conditionalError_transcript p false,
    E.posteriorSPRT_conditionalError_transcript p true]
  have hnotFalse : {record : Unit × E.StoppedWord | E.posteriorRecordDecision record ≠ false} =
      {record | E.posteriorRecordDecision record = true} := by
    ext record
    cases E.posteriorRecordDecision record <;> simp
  have hnotTrue : {record : Unit × E.StoppedWord | E.posteriorRecordDecision record ≠ true} =
      {record | E.posteriorRecordDecision record = false} := by
    ext record
    cases E.posteriorRecordDecision record <;> simp
  rw [hnotFalse, hnotTrue]
  exact add_comm _ _

theorem posteriorSPRT_bayesError_le (E : BinaryExperiment) (p : ℚ) (hp : 0 < p) (hpquarter : p ≤ 1 / 4) :
    E.bayesError (Measure.dirac ()) (E.posteriorSPRT p) ≤ ENNReal.ofReal (p : ℝ) := by
  have ha := posteriorThreshold_nonneg p hp hpquarter
  have hplt : p < 1 := by linarith
  let μ := E.transcriptLaw (Measure.dirac ()) (E.posteriorSPRT p) false
  have hfinite : ∀ x, E.expectedSamples (Measure.dirac ()) (E.posteriorSPRT p) x ≠ ⊤ :=
    E.posteriorSPRT_expectedSamples_finite p ha
  have hmass : ∫⁻ record : Unit × E.StoppedWord, E.transcriptLikelihood true record ∂μ = 1 := by
    have htrue := E.transcriptLaw_withDensity (Measure.dirac ()) (E.posteriorSPRT p) true hfinite
    have h := congrArg (fun law : Measure (Unit × E.StoppedWord) => law Set.univ) htrue
    simpa only [Bool.not_true, measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h.symm
  rw [E.bayesError_posteriorSPRT_eq_integral p ha]
  calc
    _ ≤ ∫⁻ record : Unit × E.StoppedWord, ENNReal.ofReal (p : ℝ) *
        (E.priorMass false + E.priorMass true * E.transcriptLikelihood true record) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [E.stoppedWordScore_threshold_ae p ha] with record hrecord
      exact E.posteriorRecordRisk_le p hp hplt record hrecord
    _ = ENNReal.ofReal (p : ℝ) := by
      have htotalMeas : Measurable (fun record : Unit × E.StoppedWord =>
          E.priorMass false + E.priorMass true * E.transcriptLikelihood true record) :=
        measurable_const.add (measurable_const.mul (E.measurable_transcriptLikelihood true))
      rw [lintegral_const_mul _ htotalMeas,
        lintegral_add_left (f := fun _record : Unit × E.StoppedWord => E.priorMass false) measurable_const,
        lintegral_const_mul _ (E.measurable_transcriptLikelihood true), hmass]
      simp only [lintegral_const, measure_univ, mul_one]
      have hprior : E.priorMass false + E.priorMass true = 1 := by
        simpa only [Fintype.sum_bool, add_comm] using E.priorMass_sum
      rw [hprior, mul_one]

theorem posteriorSPRTGuarantee (E : BinaryExperiment) : E.PosteriorSPRTGuarantee := by
  refine ⟨E.logIncrementBound true + 2 * |Real.log (E.priorReal true / E.priorReal false)|, ?_, ?_⟩
  · have hK := E.logIncrementBound_nonneg true
    have hp := abs_nonneg (Real.log (E.priorReal true / E.priorReal false))
    linarith
  · intro p hp hpquarter
    refine ⟨E.posteriorSPRT p, E.posteriorSPRT_isPosteriorThresholdRule p,
      E.posteriorSPRT_bayesError_le p hp hpquarter, ?_⟩
    intro x
    exact ⟨E.posteriorSPRT_expectedSamples_finite p (posteriorThreshold_nonneg p hp hpquarter) x,
      E.posteriorSPRT_expectedObservationCharge_finite p (posteriorThreshold_nonneg p hp hpquarter) x,
      E.posteriorSPRT_sharpObservationCharge p hp hpquarter x⟩

end PaperProofs.Statistics.BinaryExperiment
