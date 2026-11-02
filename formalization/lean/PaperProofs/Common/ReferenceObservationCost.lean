module

public import PaperProofs.Common.ReferenceMassFlow
public import PaperProofs.Common.NativeCostBound
public import PaperProofs.Statistics.LocalUpper

/-!
Actual observation charges of the unchanged ideal reference. Charges are
suprema over all genuine run prefixes, including failed and infinite paths.
The entry decomposition and local SPRT bound below use the true joint entry
law. They do not identify the actual continuation with a fresh suffix run;
that separate execution-transport obligation is not assumed here.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance}

private theorem reportedWrite_reviews (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s i bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

theorem step_reviews_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I}
    (hs : Step input C mode accounting tapes s action next) (stage : I.Stage) :
    s.ledger.reviews stage ≤ next.ledger.reviews stage := by
  classical
  cases hs with
  | review current live port resources =>
    by_cases heq : stage = current
    · subst stage
      simp only [record, reviewLedger, Function.update_self]
      exact le_add_of_nonneg_right (by exact bot_le)
    · simp only [record, reviewLedger, Function.update_of_ne heq, le_refl]
  | write current bit live port resources => simp only [record, reportedWrite_reviews, le_refl]
  | allocate | execute | advance | stop | abandon => exact le_rfl

theorem run_reviews_mono {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (stage : I.Stage) : Monotone (fun n => (run input C mode accounting rule sample n).ledger.reviews stage) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hh : (run input C mode accounting rule sample n).halted = true
  · rw [run_succ_of_halted input C mode accounting rule sample n hh]
  · have ha : (run input C mode accounting rule sample n).halted = false := Bool.eq_false_iff.mpr hh
    obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample n
    obtain ⟨next, hs⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) m _ hp ha
    rw [run_succ_of_step input C mode accounting rule sample n next ha hs]
    exact step_reviews_mono input C mode accounting _ hs stage

/-- Paid observations on one stage, retaining every prefix and infinity. -/
noncomputable def runStageObservationBill {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (stage : I.Stage) (sample : Seed × input.World) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal (input.fees.observation stage : ℝ) *
    ((run input C mode accounting rule sample n).ledger.reviews stage : ℝ≥0∞)

theorem runObservationBill_eq_sum_stage {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World) :
    runObservationBill input C mode accounting rule sample =
      ∑ stage, runStageObservationBill input C mode accounting rule stage sample := by
  classical
  symm
  apply ENNReal.finsetSum_iSup_of_monotone
  intro stage n m hnm
  exact mul_le_mul_right (ENat.toENNReal_mono (run_reviews_mono input C mode accounting rule hlegal sample stage hnm)) _

theorem measurable_runStageObservationBill {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hrule : MeasurableRule rule)
    (stage : I.Stage) : Measurable (runStageObservationBill input C mode accounting rule stage) := by
  apply Measurable.iSup
  intro n
  exact (measurable_of_countable (fun s : State I => ENNReal.ofReal (input.fees.observation stage : ℝ) *
    (s.ledger.reviews stage : ℝ≥0∞))).comp (measurable_run input C mode accounting rule hrule n)

theorem expectedObservationBill_eq_sum_stage {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (hrule : MeasurableRule rule) (ν : Measure Seed) :
    expectedObservationBill input C mode accounting rule ν =
      ∑ stage, ∫⁻ sample, runStageObservationBill input C mode accounting rule stage sample ∂input.seededWorldLaw ν := by
  unfold expectedObservationBill
  simp_rw [runObservationBill_eq_sum_stage input C mode accounting rule hlegal]
  exact lintegral_finsetSum _ (fun stage _ => measurable_runStageObservationBill input C mode accounting rule hrule stage)

/-- The potential stop selected by the actual entry. No entry and the
non-testing infinite-rank branch both have zero observation allowance. -/
noncomputable def referenceEntrySampleBound {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (sample : Seed × input.World) : ℕ∞ :=
  match entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample with
  | none => 0
  | some history => match referenceAvailableEntryTarget input available budget history with
    | none => 0
    | some p => (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2

private theorem enat_add_one_le_of_finite_lt {a b : ℕ∞} (ha : a ≠ ⊤) (hab : a < b) : a + 1 ≤ b := by
  by_cases hb : b = ⊤
  · rw [hb]; exact le_top
  · rw [← ENat.natCast_toNat ha, ← ENat.natCast_toNat hb] at hab ⊢
    rw [← ENat.natCast_one, ← ENat.natCast_add]
    exact ENat.natCast_le_natCast.mpr (Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp hab))

/-- Every actual ideal-reference prefix obeys its own entry-selected local
stop. This is pathwise and does not assume eventual success or finite ET. -/
theorem prefix_reference_reviews_le_entrySampleBound {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (sample : Seed × input.World) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget none)
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n s) :
    ∀ stage : I.Stage, s.ledger.reviews stage ≤ referenceEntrySampleBound input C accounting available budget stage sample := by
  induction hp with
  | initial => intro stage; exact bot_le
  | @next n s next earlier hs ih =>
    generalize ha : referenceRule input available budget none sample.1 s.history = action at hs
    cases hs with
    | review current live port resources =>
      intro stage
      by_cases heq : stage = current
      · subst stage
        obtain ⟨history, p, he, ht, hlt⟩ := prefix_referenceAvailableReview_realization input C hearly accounting available budget
          hbudget hsmall sample earlier live.1 current ha
        simp only [record, reviewLedger, Function.update_self, referenceEntrySampleBound, he, ht]
        exact enat_add_one_le_of_finite_lt
          (prefix_reviews_ne_top input C .uncapped accounting (referenceRule input available budget none)
            sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier current) hlt
      · simpa only [record, reviewLedger, Function.update_of_ne heq] using ih stage
    | write current bit live port resources =>
      intro stage
      simpa only [record, reportedWrite_reviews] using ih stage
    | allocate | execute | advance | stop | abandon => exact ih

theorem referenceStageObservationBill_le_entryCharge {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage : I.Stage) (sample : Seed × input.World) :
    runStageObservationBill input C .uncapped accounting (referenceRule input available budget none) stage sample ≤
      (input.experiment stage).observationCharge (referenceEntrySampleBound input C accounting available budget stage sample) := by
  rw [input.observationCharge_agrees]
  apply iSup_le
  intro n
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (referenceRule input available budget none)
    (referenceRule_uncapped_legal input C hearly accounting available budget none) sample n
  exact mul_le_mul_right (ENat.toENNReal_mono (prefix_reference_reviews_le_entrySampleBound input C hearly accounting
    available budget hbudget hsmall sample hp stage)) _

theorem referenceStageObservationBill_zero_of_no_entry {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage : I.Stage) (sample : Seed × input.World)
    (hnone : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = none) :
    runStageObservationBill input C .uncapped accounting (referenceRule input available budget none) stage sample = 0 := by
  have h := referenceStageObservationBill_le_entryCharge input C hearly accounting available budget hbudget hsmall stage sample
  have hz : runStageObservationBill input C .uncapped accounting (referenceRule input available budget none) stage sample ≤ (0 : ℝ≥0∞) := by
    simpa only [referenceEntrySampleBound, hnone, BinaryExperiment.observationCharge_zero] using h
  exact le_antisymm hz (show (0 : ℝ≥0∞) ≤ _ from bot_le)

/-- The genuine entry atom is independent of this stage's full truth/tape.
The integrand may be infinite; no integrability or finite cost is assumed. -/
theorem lintegral_on_referenceEntry_stageFunction
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (f : input.StageSample stage → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
      f (sample.2 stage) ∂input.seededWorldLaw (Measure.dirac ())) =
      input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
        ∫⁻ localSample, f localSample ∂input.stageLaw stage := by
  classical
  let policy := referenceIdealPolicy input C hearly accounting available budget
  let μ := input.seededWorldLaw (Measure.dirac ())
  let record := entrySeedHistory input C .uncapped accounting policy.rule stage
  let atom : Set (Unit × EntryHistory I) := {((), some history)}
  let weight : Unit × EntryHistory I → ℝ≥0∞ := atom.indicator (fun _ => 1)
  let joint := fun sample : Unit × input.World => (record sample, sample.2 stage)
  let g : (Unit × EntryHistory I) × input.StageSample stage → ℝ≥0∞ := fun z => weight z.1 * f z.2
  have hr : Measurable record := measurable_entrySeedHistory input C .uncapped accounting policy.rule policy.measurable_rule stage
  have hj : Measurable joint := hr.prodMk ((measurable_pi_apply stage).comp measurable_snd)
  have hw : Measurable weight := measurable_const.indicator (measurableSet_singleton _)
  have hg : Measurable g := (hw.comp measurable_fst).mul (hf.comp measurable_snd)
  have hpoint : ∀ sample : Unit × input.World,
      (referenceEntryEvent input C accounting available budget stage history).indicator
        (fun x => f (x.2 stage)) sample = g (joint sample) := by
    intro sample
    cases hu : sample.1
    by_cases he : entryHistory input C .uncapped accounting policy.rule stage sample = some history
    · have hm : sample ∈ referenceEntryEvent input C accounting available budget stage history := he
      rw [Set.indicator_of_mem hm]
      have hrval : record sample = ((), some history) := by simp only [record, entrySeedHistory, hu, he]
      simp only [g, joint, weight, hrval, atom, Set.indicator_of_mem (Set.mem_singleton _), one_mul]
    · have hm : sample ∉ referenceEntryEvent input C accounting available budget stage history := he
      rw [Set.indicator_of_notMem hm]
      have hrval : record sample ∉ atom := by
        intro hh
        have hc : entryHistory input C .uncapped accounting policy.rule stage sample = some history :=
          congrArg Prod.snd (Set.mem_singleton_iff.mp hh)
        exact he hc
      simp only [g, joint, weight, Set.indicator_of_notMem hrval, zero_mul]
  have hmass : (μ.map record) atom = μ (referenceEntryEvent input C accounting available budget stage history) := by
    rw [Measure.map_apply hr (measurableSet_singleton _)]
    congr 1
    ext sample
    change (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) = ((), some history) ↔ _
    cases sample.1
    simp only [Prod.mk.injEq, true_and]
    rfl
  calc
    _ = ∫⁻ sample, g (joint sample) ∂μ := by
      rw [← lintegral_indicator (measurableSet_referenceEntryEvent input C accounting available budget stage history)]
      exact lintegral_congr hpoint
    _ = ∫⁻ z, g z ∂μ.map joint := (lintegral_map hg hj).symm
    _ = ∫⁻ z, g z ∂(μ.map record).prod (input.stageLaw stage) := by
      rw [entrySeedHistory_jointLaw input C .uncapped accounting policy (Measure.dirac ()) stage]
    _ = (∫⁻ r, weight r ∂μ.map record) * ∫⁻ x, f x ∂input.stageLaw stage :=
      lintegral_prod_mul hw.aemeasurable hf.aemeasurable
    _ = _ := by
      rw [show (∫⁻ r, weight r ∂μ.map record) = (μ.map record) atom by
        exact (lintegral_indicator_const (measurableSet_singleton _) 1).trans (one_mul _)]
      rw [hmass]

noncomputable def stageTestObservationCharge (input : StatisticalInput I) (stage : I.Stage)
    (test : (input.experiment stage).AdmissibleRule Unit) (sample : input.StageSample stage) : ℝ≥0∞ :=
  (input.experiment stage).observationCharge (test.rule.stop () sample.2)

theorem measurable_stageTestObservationCharge (input : StatisticalInput I) (stage : I.Stage)
    (test : (input.experiment stage).AdmissibleRule Unit) :
    Measurable (stageTestObservationCharge input stage test) := by
  have hs : Measurable (fun sample : input.StageSample stage =>
      test.rule.stop () sample.2) :=
    test.measurable_stop.comp (measurable_const.prodMk measurable_snd)
  exact (measurable_of_countable (input.experiment stage).observationCharge).comp hs

theorem stageLaw_testObservationCharge (input : StatisticalInput I) (stage : I.Stage)
    (test : (input.experiment stage).AdmissibleRule Unit) :
    (∫⁻ sample, stageTestObservationCharge input stage test sample ∂input.stageLaw stage) =
      (input.experiment stage).bayesObservationCharge (Measure.dirac ()) test := by
  let E := input.experiment stage
  let f : E.Tape → ℝ≥0∞ := fun tape => E.observationCharge (test.rule.stop () tape)
  have hf : Measurable f := (measurable_of_countable E.observationCharge).comp
    (test.measurable_stop.comp (measurable_const.prodMk measurable_id))
  have hp (truth : Bool) : (∫⁻ sample : Bool × E.Tape, f sample.2 ∂(Measure.dirac truth).prod (E.tapeLaw truth)) =
      E.expectedObservationCharge (Measure.dirac ()) test truth := by
    calc
      _ = ∫⁻ _x : Bool, ∫⁻ tape, f tape ∂E.tapeLaw truth ∂Measure.dirac truth :=
        lintegral_prod _ (hf.comp measurable_snd).aemeasurable
      _ = ∫⁻ tape, f tape ∂E.tapeLaw truth := lintegral_dirac' _ measurable_const
      _ = _ := by
        unfold BinaryExperiment.expectedObservationCharge BinaryExperiment.conditionalLaw
        symm
        calc
          _ = ∫⁻ seed : Unit, ∫⁻ tape, E.observationCharge (test.rule.stop seed tape) ∂E.tapeLaw truth
              ∂Measure.dirac () :=
            lintegral_prod _ ((measurable_of_countable E.observationCharge).comp test.measurable_stop).aemeasurable
          _ = _ := lintegral_dirac' _ (measurable_of_countable _)
  rw [StatisticalInput.stageLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp only [smul_eq_mul, stageTestObservationCharge, BinaryExperiment.bayesObservationCharge, Fintype.sum_bool]
  rw [hp true, hp false]

/-- A local testing charge bound on a genuine entry atom. It includes paths
that subsequently abandon or fail, and atoms of zero probability. -/
theorem referenceStageObservationBill_on_entry_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : referenceAvailableEntryTarget input available budget history = some p) :
    (∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
      runStageObservationBill input C .uncapped accounting (referenceRule input available budget none) stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) ≤
      input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
        (input.experiment stage).bayesObservationCharge (Measure.dirac ()) ((input.experiment stage).posteriorSPRT p) := by
  calc
    _ ≤ ∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
        stageTestObservationCharge input stage ((input.experiment stage).posteriorSPRT p) (sample.2 stage)
        ∂input.seededWorldLaw (Measure.dirac ()) := by
      apply setLIntegral_mono' (measurableSet_referenceEntryEvent input C accounting available budget stage history)
      intro sample hs
      have hb := referenceStageObservationBill_le_entryCharge input C hearly accounting available budget hbudget hsmall stage sample
      have he : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history := hs
      simpa only [referenceEntrySampleBound, he, htarget, stageTestObservationCharge, BinaryExperiment.posteriorSPRT] using hb
    _ = _ := by
      rw [lintegral_on_referenceEntry_stageFunction input C hearly accounting available budget stage history _
        (measurable_stageTestObservationCharge input stage _), stageLaw_testObservationCharge]

theorem referenceStageObservationBill_on_entry_none
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I))
    (htarget : referenceAvailableEntryTarget input available budget history = none) :
    (∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
      runStageObservationBill input C .uncapped accounting (referenceRule input available budget none) stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) = 0 := by
  apply setLIntegral_eq_zero (measurableSet_referenceEntryEvent input C accounting available budget stage history)
  intro sample hs
  have hb := referenceStageObservationBill_le_entryCharge input C hearly accounting available budget hbudget hsmall stage sample
  have he : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history := hs
  have hz : runStageObservationBill input C .uncapped accounting (referenceRule input available budget none) stage sample ≤ (0 : ℝ≥0∞) := by
    simpa only [referenceEntrySampleBound, he, htarget, BinaryExperiment.observationCharge_zero] using hb
  exact le_antisymm hz (show (0 : ℝ≥0∞) ≤ _ from bot_le)

/-- This is a local SPRT expectation, not a definition of the actual
reference cost or a recursive fresh-suffix cost. -/
noncomputable def referenceEntryLocalObservationPrice (input : StatisticalInput I)
    (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) : ℝ≥0∞ :=
  match referenceAvailableEntryTarget input available budget history with
  | none => 0
  | some p => (input.experiment stage).bayesObservationCharge (Measure.dirac ()) ((input.experiment stage).posteriorSPRT p)

theorem referenceStageObservationBill_entry_decomposition
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    (∫⁻ sample, runStageObservationBill input C .uncapped accounting (referenceRule input available budget none) stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) =
    ∑' history : List (VisibleEvent I), ∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
      runStageObservationBill input C .uncapped accounting (referenceRule input available budget none) stage sample
        ∂input.seededWorldLaw (Measure.dirac ()) :=
  lintegral_eq_tsum_referenceEntry input C accounting available budget stage _
    (measurable_runStageObservationBill input C .uncapped accounting _ (measurable_referenceRule input available budget none) stage)
    (referenceStageObservationBill_zero_of_no_entry input C hearly accounting available budget hbudget hsmall stage)

/-- All actual observation expectations, including failed paths and infinity,
are controlled by the entry-mass-weighted local tests on the original world. -/
theorem referenceExpectedObservationBill_le_entry_prices
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    expectedObservationBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      ∑ stage, ∑' history : List (VisibleEvent I),
        input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
          referenceEntryLocalObservationPrice input available budget stage history := by
  rw [expectedObservationBill_eq_sum_stage input C .uncapped accounting _
    (referenceRule_uncapped_legal input C hearly accounting available budget none)
    (measurable_referenceRule input available budget none)]
  apply Finset.sum_le_sum
  intro stage _
  rw [referenceStageObservationBill_entry_decomposition input C hearly accounting available budget hbudget hsmall stage]
  apply ENNReal.tsum_le_tsum
  intro history
  cases ht : referenceAvailableEntryTarget input available budget history with
  | none =>
    rw [referenceStageObservationBill_on_entry_none input C hearly accounting available budget hbudget hsmall stage history ht]
    exact bot_le
  | some p =>
    simpa only [referenceEntryLocalObservationPrice, ht] using
      referenceStageObservationBill_on_entry_le input C hearly accounting available budget hbudget hsmall stage history p ht

/-- The frozen local coefficient and its explicit bounded-overshoot slack,
applied to the very test that the actual entry selects. -/
theorem referenceStageObservationBill_on_entry_sharp_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : referenceAvailableEntryTarget input available budget history = some p) :
    (∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
      runStageObservationBill input C .uncapped accounting (referenceRule input available budget none) stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) ≤
      input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
        ENNReal.ofReal ((input.experiment stage).coefficient *
          (Real.log (1 / (p : ℝ)) + (input.experiment stage).logIncrementBound true +
            2 * |Real.log ((input.experiment stage).priorReal true / (input.experiment stage).priorReal false)|)) := by
  let E := input.experiment stage
  have hp := referenceAvailableEntryTarget_valid input available budget p history htarget
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.1
  have hpone : (p : ℝ) ≤ 1 := by
    have hh : (p : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hp.2
    norm_num at hh
    linarith
  have hlog : 0 ≤ Real.log (1 / (p : ℝ)) := Real.log_nonneg ((le_div_iff₀ hpR).mpr (by linarith))
  have hB : 0 ≤ Real.log (1 / (p : ℝ)) + E.logIncrementBound true +
      2 * |Real.log (E.priorReal true / E.priorReal false)| := by
    have hK := E.logIncrementBound_nonneg true
    positivity
  have hb := E.bayesObservationCharge_le_drift_bound (Measure.dirac ()) (E.posteriorSPRT p)
    _ hB (E.posteriorSPRT_expectedObservationCharge_finite p
      (BinaryExperiment.posteriorThreshold_nonneg p hp.1 hp.2))
    (fun x => by simpa only [add_assoc] using E.posteriorSPRT_sharpObservationCharge p hp.1 hp.2 x)
  exact (referenceStageObservationBill_on_entry_le input C hearly accounting available budget hbudget hsmall stage history p htarget).trans
    (mul_le_mul_right hb _)

/-- The actual total bill retains every paid correction, including those on
later failing paths. Its observation term is the entry-price sum proved above. -/
theorem referenceExpectedBill_le_entry_prices_add_corrections
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      (∑ stage, ∑' history : List (VisibleEvent I),
        input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
          referenceEntryLocalObservationPrice input available budget stage history) +
        (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  exact (expectedBill_le_observation_add input C .uncapped accounting
    (referenceIdealPolicy input C hearly accounting available budget) (Measure.dirac ())).trans
      (add_le_add (referenceExpectedObservationBill_le_entry_prices input C hearly accounting available budget hbudget hsmall) le_rfl)

/-- The actual remaining observation bill from this numeric stage onward.
It is a finite sum of costs of the original run, never a recursive value. -/
noncomputable def runRemainingObservationBill {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (first : ℕ) (sample : Seed × input.World) : ℝ≥0∞ :=
  ∑ stage : I.Stage, if first ≤ stage.val then runStageObservationBill input C mode accounting rule stage sample else 0

theorem measurable_runRemainingObservationBill {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hrule : MeasurableRule rule) (first : ℕ) :
    Measurable (runRemainingObservationBill input C mode accounting rule first) := by
  classical
  apply Finset.measurable_fun_sum
  intro stage _
  by_cases h : first ≤ stage.val
  · simpa only [ite_eq_left h] using measurable_runStageObservationBill input C mode accounting rule hrule stage
  · simpa only [ite_eq_right h] using (measurable_const : Measurable (fun _ : Seed × input.World => (0 : ℝ≥0∞)))

theorem runRemainingObservationBill_step {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (stage : I.Stage) (sample : Seed × input.World) :
    runRemainingObservationBill input C mode accounting rule stage.val sample =
      runStageObservationBill input C mode accounting rule stage sample +
        runRemainingObservationBill input C mode accounting rule (stage.val + 1) sample := by
  classical
  rw [runRemainingObservationBill, runRemainingObservationBill]
  have hsingle : runStageObservationBill input C mode accounting rule stage sample =
      ∑ current : I.Stage, if current = stage then runStageObservationBill input C mode accounting rule current sample else 0 := by simp
  rw [hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro current _
  by_cases heq : current = stage
  · subst current; simp
  · have hne : current.val ≠ stage.val := fun hh => heq (Fin.ext hh)
    by_cases hle : stage.val ≤ current.val
    · have hlt : stage.val + 1 ≤ current.val := by omega
      simp only [hle, hlt, ite_true, heq, ite_false, zero_add]
    · have hlt : ¬ stage.val + 1 ≤ current.val := by omega
      simp only [hle, hlt, ite_false, heq, add_zero]

/-- Exact branch separation of the actual continuation charge. The two
integrals are unnormalized conditional costs on the same original run.
No fresh-suffix execution identity or cost upper bound is assumed. -/
theorem referenceRemainingObservationBill_on_entry_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : referenceAvailableEntryTarget input available budget history = some p) :
    (∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
      runRemainingObservationBill input C .uncapped accounting (referenceRule input available budget none) stage.val sample
      ∂input.seededWorldLaw (Measure.dirac ())) ≤
      input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) *
          (input.experiment stage).bayesObservationCharge (Measure.dirac ()) ((input.experiment stage).posteriorSPRT p) +
        (∫⁻ sample in referenceEntryEvent input C accounting available budget stage history ∩
            referenceStageWriteError input C accounting available budget stage,
          runRemainingObservationBill input C .uncapped accounting (referenceRule input available budget none) (stage.val + 1) sample
          ∂input.seededWorldLaw (Measure.dirac ())) +
        (∫⁻ sample in referenceEntryEvent input C accounting available budget stage history \
            referenceStageWriteError input C accounting available budget stage,
          runRemainingObservationBill input C .uncapped accounting (referenceRule input available budget none) (stage.val + 1) sample
          ∂input.seededWorldLaw (Measure.dirac ())) := by
  let rule : PolicyRule I Unit := referenceRule input available budget none
  let μ := input.seededWorldLaw (Measure.dirac ())
  let A := referenceEntryEvent input C accounting available budget stage history
  let E := referenceStageWriteError input C accounting available budget stage
  let future := runRemainingObservationBill input C .uncapped accounting rule (stage.val + 1)
  have hsplit : (∫⁻ sample in A, future sample ∂μ) =
      (∫⁻ sample in A ∩ E, future sample ∂μ) + ∫⁻ sample in A \ E, future sample ∂μ := by
    rw [← lintegral_add_measure, Measure.restrict_inter_add_sdiff _
      (measurableSet_referenceStageWriteError input C accounting available budget stage)]
  have hb := referenceStageObservationBill_on_entry_le input C hearly accounting available budget hbudget hsmall stage history p htarget
  calc
    _ = (∫⁻ sample in A, runStageObservationBill input C .uncapped accounting rule stage sample ∂μ) +
        ∫⁻ sample in A, future sample ∂μ := by
      calc
        _ = ∫⁻ sample in A, runStageObservationBill input C .uncapped accounting rule stage sample + future sample ∂μ :=
          lintegral_congr (runRemainingObservationBill_step input C .uncapped accounting rule stage)
        _ = _ := lintegral_add_left (measurable_runStageObservationBill input C .uncapped accounting rule
          (measurable_referenceRule input available budget none) stage) _
    _ ≤ _ := by
      rw [hsplit]
      simpa only [add_assoc] using add_le_add hb (le_refl ((∫⁻ sample in A ∩ E, future sample ∂μ) + ∫⁻ sample in A \ E, future sample ∂μ))

end PaperProofs.Common.Native
