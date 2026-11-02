module

public import PaperProofs.Common.PSTR_ST_SelectorSuffixRun_022
public import PaperProofs.Common.PSTR_ST_SelectorObservation_026

/-! Actual entry-atom integration for inherited-selector suffix fees.
Only genuine pre-birth product laws and proved all-clock fee transport are
used. Null entry masses and infinite observation bills are retained. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Integration

open PaperProofs.Statistics

variable {I : Instance}

def selectorEntryEvent (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available)
    (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) : Set (Unit × input.World) :=
  {sample | entryHistory input C .uncapped accounting
    (MaxSelector.rule selector.choose input available budget none) stage sample = some history}

theorem measurableSet_selectorEntryEvent (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available)
    (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) :
    MeasurableSet (selectorEntryEvent input C accounting available selector budget stage history) := by
  have hm : MeasurableRule (MaxSelector.rule selector.choose input available budget none) :=
    (measurable_of_countable (fun history => MaxSelector.rule selector.choose input available budget none () history)).comp measurable_snd
  exact (measurable_entryHistory input C .uncapped accounting _ hm stage) (measurableSet_singleton (some history))

theorem lintegral_on_selectorEntry_freshSuffixFunction
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (f : (input.freshSuffix stage.val).World → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ sample in selectorEntryEvent input C accounting available selector budget stage history,
      f (input.restrictFreshWorld stage.val sample.2) ∂input.seededWorldLaw (Measure.dirac ())) =
      input.seededWorldLaw (Measure.dirac ()) (selectorEntryEvent input C accounting available selector budget stage history) *
        ∫⁻ world, f world ∂(input.freshSuffix stage.val).worldLaw := by
  classical
  let policy := policy selector.choose input C hearly accounting available budget none
  let μ := input.seededWorldLaw (Measure.dirac ())
  let record := entrySeedHistory input C .uncapped accounting policy.rule stage
  let atom : Set (Unit × EntryHistory I) := {((), some history)}
  let weight : Unit × EntryHistory I → ℝ≥0∞ := atom.indicator (fun _ => 1)
  let joint := fun sample : Unit × input.World => (record sample, input.restrictFreshWorld stage.val sample.2)
  let g : (Unit × EntryHistory I) × (input.freshSuffix stage.val).World → ℝ≥0∞ := fun z => weight z.1 * f z.2
  have hr : Measurable record := measurable_entrySeedHistory input C .uncapped accounting policy.rule policy.measurable_rule stage
  have hj : Measurable joint := hr.prodMk ((input.measurable_restrictFreshWorld stage.val).comp measurable_snd)
  have hw : Measurable weight := measurable_const.indicator (measurableSet_singleton _)
  have hg : Measurable g := (hw.comp measurable_fst).mul (hf.comp measurable_snd)
  have hpoint : ∀ sample : Unit × input.World,
      (selectorEntryEvent input C accounting available selector budget stage history).indicator
        (fun x => f (input.restrictFreshWorld stage.val x.2)) sample = g (joint sample) := by
    intro sample
    cases hu : sample.1
    by_cases he : entryHistory input C .uncapped accounting policy.rule stage sample = some history
    · have hm : sample ∈ selectorEntryEvent input C accounting available selector budget stage history := he
      rw [Set.indicator_of_mem hm]
      have hrval : record sample = ((), some history) := by simp only [record, entrySeedHistory, hu, he]
      simp only [g, joint, weight, hrval, atom, Set.indicator_of_mem (Set.mem_singleton _), one_mul]
    · have hm : sample ∉ selectorEntryEvent input C accounting available selector budget stage history := he
      rw [Set.indicator_of_notMem hm]
      have hrval : record sample ∉ atom := by
        intro hh
        exact he (congrArg Prod.snd (Set.mem_singleton_iff.mp hh))
      simp only [g, joint, weight, Set.indicator_of_notMem hrval, zero_mul]
  have hmass : (μ.map record) atom = μ (selectorEntryEvent input C accounting available selector budget stage history) := by
    rw [Measure.map_apply hr (measurableSet_singleton _)]
    congr 1
    ext sample
    change (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) = ((), some history) ↔ _
    cases sample.1
    simp only [Prod.mk.injEq, true_and]
    rfl
  calc
    _ = ∫⁻ sample, g (joint sample) ∂μ := by
      rw [← lintegral_indicator (measurableSet_selectorEntryEvent input C accounting available selector budget stage history)]
      exact lintegral_congr hpoint
    _ = ∫⁻ z, g z ∂μ.map joint := (lintegral_map hg hj).symm
    _ = ∫⁻ z, g z ∂(μ.map record).prod (input.freshSuffix stage.val).worldLaw := by
      rw [entrySeedHistory_jointFreshSuffixLaw input C .uncapped accounting policy (Measure.dirac ()) stage]
    _ = (∫⁻ r, weight r ∂μ.map record) * ∫⁻ x, f x ∂(input.freshSuffix stage.val).worldLaw :=
      lintegral_prod_mul hw.aemeasurable hf.aemeasurable
    _ = _ := by
      rw [show (∫⁻ r, weight r ∂μ.map record) = (μ.map record) atom by
        exact (lintegral_indicator_const (measurableSet_singleton _) 1).trans (one_mul _)]
      rw [hmass]

/-- Exact expected continuation fee on an actual entry atom. This uses the
proved same-world native run identity and the genuine product law, not a
Markov/freshness assumption about the controller. It retains zero entry mass,
failed/abandoned paths and infinite observation bills. Global iterated-log
bounds and the bad-child uniform bound remain separate obligations. -/
theorem selectorRemainingObservationBill_on_entry_eq_suffix
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (risk : ℚ)
    (hrisk : entryRisk selector.choose input available budget history = some risk) :
    (∫⁻ sample in selectorEntryEvent input C accounting available selector budget stage history,
      runRemainingObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage.val sample
        ∂input.seededWorldLaw (Measure.dirac ())) =
      input.seededWorldLaw (Measure.dirac ()) (selectorEntryEvent input C accounting available selector budget stage history) *
        expectedObservationBill (input.freshSuffix stage.val) (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
          (zeroNormalAccounting (I.freshSuffix stage.val))
          (MaxSelector.rule (restrict I selector.choose stage.val (historyUsed history)) (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) none)
          (Measure.dirac ()) := by
  let childInput := input.freshSuffix stage.val
  let childC := currentRelaxedContract (I.freshSuffix stage.val)
  let childAccounting := zeroNormalAccounting (I.freshSuffix stage.val)
  let childRule : PolicyRule (I.freshSuffix stage.val) Unit :=
    MaxSelector.rule (restrict I selector.choose stage.val (historyUsed history)) childInput (available \ historyUsed (I := I) history) (2 * risk) none
  let f : childInput.World → ℝ≥0∞ :=
    fun world => runObservationBill childInput childC .uncapped childAccounting childRule ((), world)
  have hm : Measurable (runObservationBill childInput childC .uncapped childAccounting childRule) :=
    measurable_runObservationBill childInput childC .uncapped childAccounting childRule
      (policy (restrict I selector.choose stage.val (historyUsed history)) childInput childC rfl childAccounting
        (available \ historyUsed (I := I) history) (2 * risk) none).measurable_rule
  have hf : Measurable f := hm.comp (measurable_const.prodMk measurable_id)
  have hdirac : expectedObservationBill childInput childC .uncapped childAccounting childRule (Measure.dirac ()) =
      ∫⁻ world, f world ∂childInput.worldLaw := by
    change (∫⁻ sample, runObservationBill childInput childC .uncapped childAccounting childRule sample
      ∂(Measure.dirac ()).prod childInput.worldLaw) = _
    rw [lintegral_prod _ hm.aemeasurable]
    exact lintegral_dirac' _ (measurable_of_countable _)
  calc
    _ = ∫⁻ sample in selectorEntryEvent input C accounting available selector budget stage history,
        f (input.restrictFreshWorld stage.val sample.2) ∂input.seededWorldLaw (Measure.dirac ()) := by
      apply setLIntegral_congr_fun (measurableSet_selectorEntryEvent input C accounting available selector budget stage history)
      intro sample hs
      exact selectorEntry_observationBill_eq_suffix input C hearly accounting available selector budget hbudget hsmall
        stage history risk hrisk sample hs
    _ = input.seededWorldLaw (Measure.dirac ()) (selectorEntryEvent input C accounting available selector budget stage history) *
        ∫⁻ world, f world ∂childInput.worldLaw :=
      lintegral_on_selectorEntry_freshSuffixFunction input C hearly accounting available selector budget stage history f hf
    _ = _ := by rw [← hdirac]
theorem lintegral_eq_tsum_selectorEntry
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ) (stage : I.Stage)
    (f : Unit × input.World → ℝ≥0∞) (hf : Measurable f)
    (hzero : ∀ sample, entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample = none → f sample = 0) :
    (∫⁻ sample, f sample ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I), ∫⁻ sample in selectorEntryEvent input C accounting available selector budget stage history,
        f sample ∂input.seededWorldLaw (Measure.dirac ()) := by
  classical
  have hsplit : ∀ sample, f sample = ∑' history : List (VisibleEvent I),
      (selectorEntryEvent input C accounting available selector budget stage history).indicator f sample := by
    intro sample
    cases he : entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample with
    | none =>
      rw [hzero sample he]
      symm
      calc
        _ = ∑' _history : List (VisibleEvent I), (0 : ℝ≥0∞) := by
          apply tsum_congr
          intro history
          apply Set.indicator_of_notMem
          intro hh
          have hnone := he.symm.trans hh
          cases hnone
        _ = 0 := tsum_zero
    | some history =>
      symm
      calc
        _ = (selectorEntryEvent input C accounting available selector budget stage history).indicator f sample := by
          apply tsum_eq_single history
          intro other hne
          apply Set.indicator_of_notMem
          intro hh
          exact hne (Option.some.inj (hh.symm.trans he))
        _ = f sample := Set.indicator_of_mem (show sample ∈ selectorEntryEvent input C accounting available selector budget stage history from he) f
  calc
    _ = ∫⁻ sample, ∑' history : List (VisibleEvent I),
        (selectorEntryEvent input C accounting available selector budget stage history).indicator f sample
          ∂input.seededWorldLaw (Measure.dirac ()) := lintegral_congr hsplit
    _ = ∑' history : List (VisibleEvent I), ∫⁻ sample,
        (selectorEntryEvent input C accounting available selector budget stage history).indicator f sample
          ∂input.seededWorldLaw (Measure.dirac ()) :=
      lintegral_tsum (fun history => (hf.indicator (measurableSet_selectorEntryEvent input C accounting available selector budget stage history)).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro history
      exact lintegral_indicator (measurableSet_selectorEntryEvent input C accounting available selector budget stage history) f


end PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Integration
