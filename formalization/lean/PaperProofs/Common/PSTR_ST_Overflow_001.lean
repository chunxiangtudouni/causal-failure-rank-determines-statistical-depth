module

public import PaperProofs.Common.ReferenceOverflowRealization

/-! B19: actual per-entry/per-truth overflow with null entries retained.
The fixed target is selected by the genuine entry record, never by success. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics

open PaperProofs.Statistics

variable {I : Instance}

set_option maxHeartbeats 1000000 in
theorem referenceStageOverflow_on_entry_truth_le (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (delta : ℝ) (hsmall : delta ≤ 1 / 2) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (stage : I.Stage) (history : List (VisibleEvent I)) (truth : Bool) :
    let ideal := referenceIdealPolicy input C hearly accounting I.tools budget
    let entered := {sample : Unit × input.World |
      entryHistory input C .uncapped accounting ideal.rule stage sample = some history ∧
      (sample.2 stage).1 = truth}
    input.seededWorldLaw (Measure.dirac ())
      (referenceStageOverflow input C hearly accounting I.tools budget (referenceQuota input exponent) stage ∩ entered) ≤
        ENNReal.ofReal (delta / (2 * I.stageCount)) * input.seededWorldLaw (Measure.dirac ()) entered := by
  let policy := referenceIdealPolicy input C hearly accounting I.tools budget
  let μ := input.seededWorldLaw (Measure.dirac ())
  let record := entrySeedHistory input C .uncapped accounting policy.rule stage
  let joint := fun sample : Unit × input.World => (record sample, sample.2 stage)
  let entered := {sample : Unit × input.World |
    entryHistory input C .uncapped accounting policy.rule stage sample = some history ∧
    (sample.2 stage).1 = truth}
  let truthSet : Set (input.StageSample stage) := {truth} ×ˢ Set.univ
  let entryRect : Set ((Unit × EntryHistory I) × input.StageSample stage) :=
    {((), some history)} ×ˢ truthSet
  have hrecord : Measurable record := measurable_entrySeedHistory input C .uncapped accounting policy.rule policy.measurable_rule stage
  have hjoint : Measurable joint := hrecord.prodMk ((measurable_pi_apply stage).comp measurable_snd)
  have htruth : MeasurableSet truthSet := (measurableSet_singleton _).prod MeasurableSet.univ
  have hentryRect : MeasurableSet entryRect := (measurableSet_singleton _).prod htruth
  have hentered : entered = joint ⁻¹' entryRect := by
    ext sample
    cases sample with | mk seed world =>
      cases seed
      simp [entered, joint, record, entrySeedHistory, entryRect, truthSet]
  have hmass : μ entered = (μ.map record) {((), some history)} * (input.experiment stage).priorMass truth := by
    rw [hentered, ← Measure.map_apply hjoint hentryRect]
    rw [entrySeedHistory_jointLaw input C .uncapped accounting policy (Measure.dirac ()) stage]
    rw [Measure.prod_prod, input.stageLaw_truth_tape]
    simp only [measure_univ, mul_one]
    rfl
  cases ht : referenceEntryTarget input budget history with
  | none =>
    have hempty : referenceStageOverflow input C hearly accounting I.tools budget (referenceQuota input exponent) stage ∩ entered = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro sample hs
      obtain ⟨p, hp, _⟩ := referenceStageOverflow_subset_entryPosteriorOverflow input C hearly accounting budget
        choice.positive choice.small (referenceQuota input exponent) stage hs.1
      change entryGatedTarget (referenceEntryChoice input budget)
        (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) = some p at hp
      rw [hs.2.1] at hp
      change referenceEntryTarget input budget history = some p at hp
      rw [ht] at hp
      cases hp
    change μ (_ ∩ entered) ≤ _ * μ entered
    rw [hempty, measure_empty]
    exact zero_le
  | some p =>
    let tapes : Set (input.experiment stage).Tape :=
      {tape | (referenceQuota input exponent stage : ℕ∞) < (input.experiment stage).posteriorThresholdStop p tape}
    let rectangle : Set ((Unit × EntryHistory I) × input.StageSample stage) :=
      {((), some history)} ×ˢ ({truth} ×ˢ tapes)
    have htapes : MeasurableSet tapes := by
      exact (Set.to_countable (Set.Ioi (referenceQuota input exponent stage : ℕ∞))).measurableSet.preimage
        ((input.experiment stage).measurable_posteriorThresholdStop p)
    have hrectangle : MeasurableSet rectangle := (measurableSet_singleton _).prod ((measurableSet_singleton _).prod htapes)
    have hsubset : referenceStageOverflow input C hearly accounting I.tools budget (referenceQuota input exponent) stage ∩ entered ⊆ joint ⁻¹' rectangle := by
      intro sample hs
      obtain ⟨q, hq, hoverflow⟩ := referenceStageOverflow_subset_entryPosteriorOverflow input C hearly accounting budget
        choice.positive choice.small (referenceQuota input exponent) stage hs.1
      change entryGatedTarget (referenceEntryChoice input budget)
        (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) = some q at hq
      rw [hs.2.1] at hq
      change referenceEntryTarget input budget history = some q at hq
      have hqp : q = p := Option.some.inj (hq.symm.trans ht)
      subst q
      refine ⟨?_, ?_⟩
      · change (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) ∈ {((), some history)}
        rw [hs.2.1]
        cases sample.1
        exact Set.mem_singleton _
      · exact ⟨hs.2.2, hoverflow⟩
    have hvalid := referenceEntryTarget_bounds input budget p choice.positive choice.small history ht
    have hrisk : (0 : ℝ) < budget := by exact_mod_cast choice.positive
    have hminimal := BinaryExperiment.quotaExponent_minimal budget choice.positive I.stageCount
    rw [choice.same_exponent] at hminimal
    have hfloor : (budget : ℝ) / (referenceQuotaConstant I.stageCount : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hvalid.2.2
    have hN : 0 < I.stageCount := by
      have hs : stage.val < I.stageCount := stage.isLt
      omega
    have htape : (input.experiment stage).tapeLaw truth tapes ≤ ENNReal.ofReal (delta / (2 * I.stageCount)) := by
      refine ((input.experiment stage).rationalQuota_overflow_le p hvalid.1 hvalid.2.1
        (budget : ℝ) hrisk (choice.conservative.trans hsmall) I.stageCount hN exponent hminimal.2.1 hfloor truth).trans ?_
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right choice.conservative (by positivity))
    change μ (_ ∩ entered) ≤ _ * μ entered
    calc
      _ ≤ μ (joint ⁻¹' rectangle) := measure_mono hsubset
      _ = (μ.map joint) rectangle := (Measure.map_apply hjoint hrectangle).symm
      _ = ((μ.map record).prod (input.stageLaw stage)) rectangle := by
        rw [entrySeedHistory_jointLaw input C .uncapped accounting policy (Measure.dirac ()) stage]
      _ = (μ.map record) {((), some history)} * ((input.experiment stage).priorMass truth *
          (input.experiment stage).tapeLaw truth tapes) := by
        rw [Measure.prod_prod, input.stageLaw_truth_tape]
      _ ≤ (μ.map record) {((), some history)} * ((input.experiment stage).priorMass truth *
          ENNReal.ofReal (delta / (2 * I.stageCount))) :=
        mul_le_mul_right (mul_le_mul_right htape _) _
      _ = ENNReal.ofReal (delta / (2 * I.stageCount)) * μ entered := by rw [hmass]; ring

theorem referenceConditionalOverflowGuarantee (input : StatisticalInput I) : ReferenceConditionalOverflowGuarantee input := by
  intro C hearly accounting delta exponent budget _hd hsmall choice stage history truth
  exact referenceStageOverflow_on_entry_truth_le input C hearly accounting delta hsmall exponent budget choice stage history truth

theorem referenceOverflowClaims (input : StatisticalInput I) : ReferenceOverflowClaims input :=
  ⟨referenceOverflowIdentification input, referenceConditionalOverflowGuarantee input, referenceOverflowGuarantee input⟩

end PaperProofs.Common.Native.PSTRStatistics
