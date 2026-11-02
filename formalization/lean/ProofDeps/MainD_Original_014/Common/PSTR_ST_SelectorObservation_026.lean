module

public import Common.PSTR_ST_SelectorOrigin_025
public import PaperProofs.Common.ReferenceCostAsymptotics
public import PaperProofs.Common.NativeHeadTest

/-! Actual paid observation bounds for a fixed certified selector. The
first-stage allowance is exactly the original empty-history SPRT price,
independent of the later maximizing tie, and retains all failed paths. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Fees

open PaperProofs.Statistics

variable {I : Instance}

private theorem reportedWrite_reviews (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s i bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

noncomputable def selectorEntrySampleBound  (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ) (stage : I.Stage)
    (sample : Unit × input.World) : ℕ∞ :=
  match entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample with
  | none => 0
  | some history => match Origin.selectorEntryTarget input available selector budget history with
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
theorem prefix_selector_reviews_le_entrySampleBound  (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (sample : Unit × input.World) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none)
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n s) :
    ∀ stage : I.Stage, s.ledger.reviews stage ≤ selectorEntrySampleBound input C accounting available selector budget stage sample := by
  induction hp with
  | initial => intro stage; exact bot_le
  | @next n s next earlier hs ih =>
    generalize ha : MaxSelector.rule selector.choose input available budget none sample.1 s.history = action at hs
    cases hs with
    | review current live port resources =>
      intro stage
      by_cases heq : stage = current
      · subst stage
        obtain ⟨history, p, he, ht, hlt⟩ := Origin.prefix_selectorReview_realization input C hearly accounting available selector budget
          hbudget hsmall sample earlier live.1 current ha
        simp only [record, reviewLedger, Function.update_self, selectorEntrySampleBound, he, ht]
        exact enat_add_one_le_of_finite_lt
          (prefix_reviews_ne_top input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none)
            sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier current) hlt
      · simpa only [record, reviewLedger, Function.update_of_ne heq] using ih stage
    | write current bit live port resources =>
      intro stage
      simpa only [record, reportedWrite_reviews] using ih stage
    | allocate | execute | advance | stop | abandon => exact ih

theorem selectorStageObservationBill_le_entryCharge  (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage : I.Stage) (sample : Unit × input.World) :
    runStageObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample ≤
      (input.experiment stage).observationCharge (selectorEntrySampleBound input C accounting available selector budget stage sample) := by
  rw [input.observationCharge_agrees]
  apply iSup_le
  intro n
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none)
    (rule_uncapped_legal selector.choose input C hearly accounting available budget none) sample n
  exact mul_le_mul_right (ENat.toENNReal_mono (prefix_selector_reviews_le_entrySampleBound input C hearly accounting
    available selector budget hbudget hsmall sample hp stage)) _

theorem selectorStageObservationBill_zero_of_no_entry  (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage : I.Stage) (sample : Unit × input.World)
    (hnone : entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample = none) :
    runStageObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample = 0 := by
  have h := selectorStageObservationBill_le_entryCharge input C hearly accounting available selector budget hbudget hsmall stage sample
  have hz : runStageObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample ≤ (0 : ℝ≥0∞) := by
    simpa only [selectorEntrySampleBound, hnone, BinaryExperiment.observationCharge_zero] using h
  exact le_antisymm hz (show (0 : ℝ≥0∞) ≤ _ from bot_le)


theorem selectorEntryTarget_initial (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    Origin.selectorEntryTarget input available selector budget [] =
      referenceAvailableEntryTarget input available budget [] := by
  simp only [Origin.selectorEntryTarget, referenceAvailableEntryTarget,
    replay_initial (selector := selector) input available budget hbudget hsmall,
    referenceAvailableReplay_initial input available budget hbudget hsmall]

/-- The unchanged empty-entry SPRT price bounds all actual first-stage paid
observations uniformly in the later fixed maximizing tie. Current-allocation,
successful termination and finite expected cost are not hypotheses. -/
theorem selectorInitialStageObservationBill_le_localPrice (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first : I.Stage) (hfirst : first.val = 0) :
    (∫⁻ sample, runStageObservationBill input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) first sample
      ∂input.seededWorldLaw (Measure.dirac ())) ≤
      referenceEntryLocalObservationPrice input available budget first [] := by
  have hinitial := selectorEntryTarget_initial input available selector budget hbudget hsmall
  have hentry (sample : Unit × input.World) := entryHistory_stageZero input C .uncapped accounting
    (MaxSelector.rule selector.choose input available budget none) first hfirst sample
  cases ht : referenceAvailableEntryTarget input available budget [] with
  | none =>
    have hzero (sample : Unit × input.World) :
        runStageObservationBill input C .uncapped accounting
          (MaxSelector.rule selector.choose input available budget none) first sample = 0 := by
      have hb := selectorStageObservationBill_le_entryCharge input C hearly accounting available selector
        budget hbudget hsmall first sample
      have hle : runStageObservationBill input C .uncapped accounting
          (MaxSelector.rule selector.choose input available budget none) first sample ≤ 0 := by
        simpa only [selectorEntrySampleBound, hentry sample, hinitial, ht,
          BinaryExperiment.observationCharge_zero] using hb
      exact le_antisymm hle bot_le
    simp only [hzero, lintegral_zero, referenceEntryLocalObservationPrice, ht, le_rfl]
  | some p =>
    simp only [referenceEntryLocalObservationPrice, ht]
    rw [bayesObservationCharge_eq_seededWorld_integral input first (Measure.dirac ())
      ((input.experiment first).posteriorSPRT p)]
    apply lintegral_mono
    intro sample
    have hb := selectorStageObservationBill_le_entryCharge input C hearly accounting available selector
      budget hbudget hsmall first sample
    have hw : worldTapes input sample.2 first = (sample.2 first).2 := by funext k; rfl
    simpa only [selectorEntrySampleBound, hentry sample, hinitial, ht,
      BinaryExperiment.posteriorSPRT, hw] using hb

end PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Fees
