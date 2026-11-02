module

public import PaperProofs.Paid.PDLower_Posterior_005
public import PaperProofs.Paid.PDLower_Posterior_007
public import PaperProofs.Paid.PDLower_Allowance_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem pastEntryTest_posterior_eq_of_finite (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed)
    (stage : P.sharedInstance.Stage) (sample : Seed × (P.input fee hf).World)
    (hfinite : P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage ≠ ⊤) :
    P.binarySymmetric.wordPosteriorError
      (P.binarySymmetric.experiment.stoppedTranscript (pastEntryTest P fee hf C accounting source stage)
        ((P.input fee hf).preBirthView stage sample, (sample.2 stage).2)).2 =
      P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage := by
  have hstop := pastEntryTest_stop_eq_count P fee hf C accounting source stage sample
  change P.binarySymmetric.wordPosteriorError
    ⟨((pastEntryTest P fee hf C accounting source stage).rule.stop
      ((P.input fee hf).preBirthView stage sample) (sample.2 stage).2).toNat, fun k => (sample.2 stage).2 k.val⟩ = _
  rw [hstop]
  by_cases hz : P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage = 0
  · rw [P.paidRunPosteriorError_zero fee hf C .uncapped accounting source.rule sample stage hz, hz]
    have he : (⟨(0 : ℕ∞).toNat, fun k => (sample.2 stage).2 k.val⟩ : P.binarySymmetric.experiment.StoppedWord) = ⟨0, Fin.elim0⟩ := by
      congr 1
      funext k
      exact Fin.elim0 k
    rw [he, P.binarySymmetric.wordPosteriorError_empty]
  · simp only [Parameters.paidRunPosteriorError, hz, hfinite, ↓reduceIte]

theorem markedPosterior_stage_lower_uncapped (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    (∫⁻ sample, (P.survivingEntry fee hf C .uncapped accounting source.rule stage).indicator
      (fun sample => ENNReal.ofReal (P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage)) sample
        ∂(P.input fee hf).seededWorldLaw ν) ≤
      (P.input fee hf).seededWorldLaw ν (P.markedErrorEvent fee hf C .uncapped accounting source.rule stage) := by
  classical
  obtain ⟨gate, hgate, hfactor⟩ := survivingEntry_preBirthGate P fee hf C .uncapped accounting source stage
  let seeds : Set (Seed × (P.input fee hf).PastWorld stage) := {past | gate past = true}
  have hseeds : MeasurableSet seeds := hgate (measurableSet_singleton true)
  let B : Set ((Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.StoppedWord) := seeds ×ˢ Set.univ
  have hB : MeasurableSet B := hseeds.prod MeasurableSet.univ
  let test := pastEntryTest P fee hf C accounting source stage
  let decision := completedRecordDecision P fee hf C accounting source stage
  have hd : Measurable decision := measurable_completedRecordDecision P fee hf C accounting source stage
  let post : (Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.StoppedWord → ℝ≥0∞ :=
    B.indicator (fun record => ENNReal.ofReal (P.binarySymmetric.wordPosteriorError record.2))
  have hpost : Measurable post :=
    ((measurable_of_countable (fun word => ENNReal.ofReal (P.binarySymmetric.wordPosteriorError word))).comp measurable_snd).indicator hB
  let finite : Set ((Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.Tape) :=
    {pair | test.rule.stop pair.1 pair.2 ≠ ⊤}
  have hfinite : MeasurableSet finite := (test.measurable_stop (measurableSet_singleton (⊤ : ℕ∞))).compl
  let projection : ((Seed × (P.input fee hf).PastWorld stage) × (Bool × P.binarySymmetric.experiment.Tape)) →
      ((Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.Tape) := fun data => (data.1, data.2.2)
  have hprojection : Measurable projection := measurable_fst.prodMk measurable_snd.snd
  let F : (Seed × (P.input fee hf).PastWorld stage) × (Bool × P.binarySymmetric.experiment.Tape) → ℝ≥0∞ :=
    fun data => finite.indicator (fun pair => post (P.binarySymmetric.experiment.stoppedTranscript test pair)) (projection data)
  have hF : Measurable F := ((hpost.comp (P.binarySymmetric.experiment.measurable_stoppedTranscript test)).indicator hfinite).comp hprojection
  have hFactual (sample : Seed × (P.input fee hf).World) :
      F ((P.input fee hf).preBirthView stage sample, sample.2 stage) =
        (P.survivingEntry fee hf C .uncapped accounting source.rule stage).indicator
          (fun sample => ENNReal.ofReal (P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage)) sample := by
    let pair : (Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.Tape :=
      ((P.input fee hf).preBirthView stage sample, (sample.2 stage).2)
    have hstop : test.rule.stop pair.1 pair.2 = P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage :=
      pastEntryTest_stop_eq_count P fee hf C accounting source stage sample
    by_cases hc : P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage = ⊤
    · have hn : pair ∉ finite := by change ¬ test.rule.stop pair.1 pair.2 ≠ ⊤; exact not_not_intro (hstop.trans hc)
      change finite.indicator _ pair = _
      rw [Set.indicator_of_notMem hn]
      by_cases hs : sample ∈ P.survivingEntry fee hf C .uncapped accounting source.rule stage
      · rw [Set.indicator_of_mem hs,
          P.paidRunPosteriorError_infinite fee hf C .uncapped accounting source.rule sample stage hc,
          ENNReal.ofReal_zero]
      · rw [Set.indicator_of_notMem hs]
    · have hm : pair ∈ finite := by change test.rule.stop pair.1 pair.2 ≠ ⊤; rw [hstop]; exact hc
      change finite.indicator _ pair = _
      rw [Set.indicator_of_mem hm]
      have hp := pastEntryTest_posterior_eq_of_finite P fee hf C accounting source stage sample hc
      by_cases hs : sample ∈ P.survivingEntry fee hf C .uncapped accounting source.rule stage
      · have hb : P.binarySymmetric.experiment.stoppedTranscript test pair ∈ B := ⟨(hfactor sample).mp hs, Set.mem_univ _⟩
        change B.indicator _ (P.binarySymmetric.experiment.stoppedTranscript test pair) = _
        rw [Set.indicator_of_mem hb, Set.indicator_of_mem hs]
        exact congrArg ENNReal.ofReal hp
      · have hb : P.binarySymmetric.experiment.stoppedTranscript test pair ∉ B := by
          rintro ⟨hseed, _⟩
          exact hs ((hfactor sample).mpr hseed)
        change B.indicator _ (P.binarySymmetric.experiment.stoppedTranscript test pair) = _
        rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hs]
  have hleft : (∫⁻ sample, (P.survivingEntry fee hf C .uncapped accounting source.rule stage).indicator
        (fun sample => ENNReal.ofReal (P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage)) sample
          ∂(P.input fee hf).seededWorldLaw ν) =
      ∫⁻ record, post record ∂finiteBayesStoppedLaw P.binarySymmetric (pastSeedLaw P fee hf ν stage) test := by
    calc
      _ = ∫⁻ sample, F ((P.input fee hf).preBirthView stage sample, sample.2 stage) ∂(P.input fee hf).seededWorldLaw ν :=
        lintegral_congr (fun sample => (hFactual sample).symm)
      _ = _ := by
        rw [lintegral_preBirth_current P fee hf ν stage F hF, lintegral_finiteBayesStoppedLaw _ _ _ post hpost]
  rw [hleft]
  have hlower := finitePosterior_error_measure_lower P.binarySymmetric (pastSeedLaw P fee hf ν stage) test decision hd B hB
  apply hlower.trans
  let error (x : Bool) : Set ((Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.Tape) :=
    {pair | test.rule.stop pair.1 pair.2 ≠ ⊤ ∧ P.binarySymmetric.experiment.stoppedTranscript test pair ∈ B ∧
      decision (P.binarySymmetric.experiment.stoppedTranscript test pair) ≠ x}
  have herror (x : Bool) : MeasurableSet (error x) :=
    hfinite.inter ((hB.preimage (P.binarySymmetric.experiment.measurable_stoppedTranscript test)).inter
      (((hd.comp (P.binarySymmetric.experiment.measurable_stoppedTranscript test)) (measurableSet_singleton x)).compl))
  let localG : Bool × ((Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.Tape) → ℝ≥0∞ :=
    fun data => (error data.1).indicator (fun _ => 1) data.2
  have hlocalG : Measurable localG := by
    apply measurable_from_prod_countable_right
    intro x
    exact measurable_const.indicator (herror x)
  let G : (Seed × (P.input fee hf).PastWorld stage) × (Bool × P.binarySymmetric.experiment.Tape) → ℝ≥0∞ :=
    fun data => localG (data.2.1, projection data)
  have hG : Measurable G := hlocalG.comp (measurable_snd.fst.prodMk hprojection)
  have hGactual (sample : Seed × (P.input fee hf).World) :
      G ((P.input fee hf).preBirthView stage sample, sample.2 stage) ≤
        (P.markedErrorEvent fee hf C .uncapped accounting source.rule stage).indicator (fun _ => (1 : ℝ≥0∞)) sample := by
    let pair : (Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.Tape :=
      ((P.input fee hf).preBirthView stage sample, (sample.2 stage).2)
    change (error (sample.2 stage).1).indicator (fun _ => 1) pair ≤ _
    by_cases he : pair ∈ error (sample.2 stage).1
    · have hc : P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage ≠ ⊤ := by
        rw [← pastEntryTest_stop_eq_count P fee hf C accounting source stage sample]
        exact he.1
      have hm : sample ∈ P.markedErrorEvent fee hf C .uncapped accounting source.rule stage := by
        refine ⟨(hfactor sample).mpr he.2.1.1, ?_⟩
        rw [← completedRecordDecision_actual_of_finite P fee hf C accounting source stage sample hc]
        exact he.2.2
      rw [Set.indicator_of_mem he, Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem he]
      exact bot_le
  calc
    _ = ∫⁻ sample, G ((P.input fee hf).preBirthView stage sample, sample.2 stage) ∂(P.input fee hf).seededWorldLaw ν := by
      rw [lintegral_preBirth_current P fee hf ν stage G hG]
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      change (P.binarySymmetric.experiment.conditionalLaw (pastSeedLaw P fee hf ν stage) x) (error x) =
        ∫⁻ pair, (error x).indicator (fun _ => (1 : ℝ≥0∞)) pair
          ∂P.binarySymmetric.experiment.conditionalLaw (pastSeedLaw P fee hf ν stage) x
      rw [lintegral_indicator_const (herror x), one_mul]
    _ ≤ ∫⁻ sample, (P.markedErrorEvent fee hf C .uncapped accounting source.rule stage).indicator
        (fun _ => (1 : ℝ≥0∞)) sample ∂(P.input fee hf).seededWorldLaw ν := lintegral_mono hGactual
    _ = _ := by rw [lintegral_indicator_const (measurableSet_markedErrorEvent P fee hf C .uncapped accounting source.rule source.measurable_rule stage), one_mul]

end PDLower
