module

public import PaperProofs.Common.NativeCausality
public import PaperProofs.Statistics.RationalQuota

/-!
Statistical kernels on the potential next-stage tape. The conditioning record
retains both the actual entry history and arbitrary private seed. None records
remain in the joint law. This does not yet identify a Native reference policy
that executes the selected posterior test.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace PaperProofs.Common.Native

variable {I : Instance}

/-- The selected-target codomain is countable and carries its discrete sigma algebra. -/
instance : MeasurableSpace (Option ℚ) := ⊤
instance : MeasurableSingletonClass (Option ℚ) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

section EntryRecord

variable {Seed : Type} [MeasurableSpace Seed]

noncomputable def entrySeedHistory (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (sample : Seed × input.World) : Seed × EntryHistory I :=
  (sample.1, entryHistory input C mode accounting rule next sample)

theorem measurable_entrySeedHistory (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hrule : MeasurableRule rule) (next : I.Stage) :
    Measurable (entrySeedHistory input C mode accounting rule next) :=
  measurable_fst.prodMk (measurable_entryHistory input C mode accounting rule hrule next)

/-- Joint independence is needed when the chosen target uses the private seed.
Independence of entry history alone would not justify that choice. -/
theorem entrySeedHistory_independent_next (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (next : I.Stage) :
    IndepFun (entrySeedHistory input C mode accounting policy.rule next)
      (fun sample : Seed × input.World => sample.2 next) (input.seededWorldLaw ν) := by
  obtain ⟨record, hrecord, hpointwise⟩ := (nativePreBirthFactorization input C mode accounting)
    Seed ‹MeasurableSpace Seed› policy next
  let jointRecord : Seed × input.PastWorld next → Seed × EntryHistory I :=
    fun sample => (sample.1, record sample)
  have hm : Measurable jointRecord := measurable_fst.prodMk hrecord
  have hind := input.preBirthRecord_independent_next ν next jointRecord hm
  have heq : entrySeedHistory input C mode accounting policy.rule next =
      fun sample => jointRecord (input.preBirthView next sample) := by
    funext sample
    simp only [entrySeedHistory, jointRecord, StatisticalInput.preBirthView, hpointwise sample]
  rw [heq]
  exact hind

theorem entrySeedHistory_jointLaw (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (next : I.Stage) :
    (input.seededWorldLaw ν).map (fun sample =>
        (entrySeedHistory input C mode accounting policy.rule next sample, sample.2 next)) =
      ((input.seededWorldLaw ν).map (entrySeedHistory input C mode accounting policy.rule next)).prod
        (input.stageLaw next) := by
  have hind := entrySeedHistory_independent_next input C mode accounting policy ν next
  have hnext : Measurable (fun sample : Seed × input.World => sample.2 next) :=
    (measurable_pi_apply next).comp measurable_snd
  rw [hind.map_prod_eq_prod_map_map
    (measurable_entrySeedHistory input C mode accounting policy.rule policy.measurable_rule next).aemeasurable
    hnext.aemeasurable, input.seededWorldLaw_coordinate]

end EntryRecord

def fixedPosteriorError (input : StatisticalInput I) (next : I.Stage) (target : ℚ) :
    Set (input.StageSample next) :=
  {sample | ((input.experiment next).posteriorSPRT target).rule.decision () sample.2 ≠ sample.1}

def fixedPosteriorOverflow (input : StatisticalInput I) (next : I.Stage) (target : ℚ) (quota : ℕ) :
    Set (input.StageSample next) :=
  {sample | (quota : ℕ∞) < ((input.experiment next).posteriorSPRT target).rule.stop () sample.2}

private theorem measurable_stageDecision {E : PaperProofs.Statistics.BinaryExperiment}
    (test : E.AdmissibleRule Unit) :
    Measurable (fun sample : Bool × E.Tape => test.rule.decision () sample.2) := by
  have hp : Measurable (fun sample : Bool × E.Tape => ((), sample.2)) :=
    measurable_const.prodMk measurable_snd
  exact test.measurable_decision.comp hp

private theorem measurable_stageStop {E : PaperProofs.Statistics.BinaryExperiment}
    (test : E.AdmissibleRule Unit) :
    Measurable (fun sample : Bool × E.Tape => test.rule.stop () sample.2) := by
  have hp : Measurable (fun sample : Bool × E.Tape => ((), sample.2)) :=
    measurable_const.prodMk measurable_snd
  exact test.measurable_stop.comp hp

theorem measurableSet_fixedPosteriorError (input : StatisticalInput I) (next : I.Stage) (target : ℚ) :
    MeasurableSet (fixedPosteriorError input next target) := by
  have hm := measurable_stageDecision ((input.experiment next).posteriorSPRT target)
  exact (measurableSet_eq_fun hm measurable_fst).compl

theorem measurableSet_fixedPosteriorOverflow (input : StatisticalInput I) (next : I.Stage) (target : ℚ) (quota : ℕ) :
    MeasurableSet (fixedPosteriorOverflow input next target quota) := by
  have hm := measurable_stageStop ((input.experiment next).posteriorSPRT target)
  exact (Set.to_countable (Set.Ioi (quota : ℕ∞))).measurableSet.preimage hm

theorem conditionalError_tape (input : StatisticalInput I) (next : I.Stage) (target : ℚ) (truth : Bool) :
    (input.experiment next).conditionalError (Measure.dirac ()) ((input.experiment next).posteriorSPRT target) truth =
      (input.experiment next).tapeLaw truth {tape |
        ((input.experiment next).posteriorSPRT target).rule.decision () tape ≠ truth} := by
  change (Measure.dirac ()).prod ((input.experiment next).tapeLaw truth)
    {sample : Unit × (input.experiment next).Tape |
      ((input.experiment next).posteriorSPRT target).rule.decision sample.1 sample.2 ≠ truth} = _
  have heq : {sample : Unit × (input.experiment next).Tape |
        ((input.experiment next).posteriorSPRT target).rule.decision sample.1 sample.2 ≠ truth} =
      Set.univ ×ˢ {tape | ((input.experiment next).posteriorSPRT target).rule.decision () tape ≠ truth} := by
    ext sample
    rcases sample with ⟨⟨⟩, tape⟩
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
  rw [heq, Measure.prod_prod, measure_univ, one_mul]

theorem stageLaw_fixedPosteriorError (input : StatisticalInput I) (next : I.Stage) (target : ℚ) :
    input.stageLaw next (fixedPosteriorError input next target) =
      (input.experiment next).bayesError (Measure.dirac ()) ((input.experiment next).posteriorSPRT target) := by
  have hm := measurableSet_fixedPosteriorError input next target
  have hprod (truth : Bool) : (Measure.dirac truth).prod ((input.experiment next).tapeLaw truth)
      (fixedPosteriorError input next target) =
        (input.experiment next).tapeLaw truth {tape |
          ((input.experiment next).posteriorSPRT target).rule.decision () tape ≠ truth} := by
    rw [Measure.prod_apply hm]
    exact lintegral_dirac _ _
  rw [StatisticalInput.stageLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul, hprod]
  unfold PaperProofs.Statistics.BinaryExperiment.bayesError
  rw [Fintype.sum_bool, conditionalError_tape, conditionalError_tape]

theorem stageLaw_fixedPosteriorError_le (input : StatisticalInput I) (next : I.Stage) (target : ℚ)
    (htarget : 0 < target) (hquarter : target ≤ 1 / 4) :
    input.stageLaw next (fixedPosteriorError input next target) ≤ ENNReal.ofReal (target : ℝ) := by
  rw [stageLaw_fixedPosteriorError]
  exact (input.experiment next).posteriorSPRT_bayesError_le target htarget hquarter

theorem stageLaw_fixedPosteriorOverflow_le (input : StatisticalInput I) (next : I.Stage) (target : ℚ)
    (htarget : 0 < target) (hquarter : target ≤ 1 / 4) (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N) (exponent : ℕ)
    (hqualifies : PaperProofs.Statistics.DyadicQualifies
      (2 * N * PaperProofs.Statistics.referenceQuotaConstant N) delta exponent)
    (hfloor : delta / (PaperProofs.Statistics.referenceQuotaConstant N : ℝ) ≤ (target : ℝ)) :
    input.stageLaw next (fixedPosteriorOverflow input next target ((input.experiment next).rationalQuota exponent)) ≤
      ENNReal.ofReal (delta / (2 * N)) := by
  have hm := measurableSet_fixedPosteriorOverflow input next target ((input.experiment next).rationalQuota exponent)
  have hprod (truth : Bool) : (Measure.dirac truth).prod ((input.experiment next).tapeLaw truth)
      (fixedPosteriorOverflow input next target ((input.experiment next).rationalQuota exponent)) =
        (input.experiment next).tapeLaw truth {tape |
          (((input.experiment next).rationalQuota exponent : ℕ) : ℕ∞) <
            ((input.experiment next).posteriorSPRT target).rule.stop () tape} := by
    rw [Measure.prod_apply hm]
    exact lintegral_dirac _ _
  rw [StatisticalInput.stageLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul, hprod]
  have ht := (input.experiment next).rationalQuota_overflow_le target htarget hquarter delta hdelta hsmall N hN exponent hqualifies hfloor true
  have hf := (input.experiment next).rationalQuota_overflow_le target htarget hquarter delta hdelta hsmall N hN exponent hqualifies hfloor false
  calc
    _ ≤ (input.experiment next).priorMass true * ENNReal.ofReal (delta / (2 * N)) +
        (input.experiment next).priorMass false * ENNReal.ofReal (delta / (2 * N)) :=
      add_le_add (mul_le_mul_of_nonneg_left ht zero_le) (mul_le_mul_of_nonneg_left hf zero_le)
    _ = _ := by
      rw [← add_mul]
      have hprior : (input.experiment next).priorMass true + (input.experiment next).priorMass false = 1 := by
        simpa only [Fintype.sum_bool] using (input.experiment next).priorMass_sum
      rw [hprior, one_mul]

section CountableTargets

variable {Record : Type*} [MeasurableSpace Record]

def selectedPosteriorError (input : StatisticalInput I) (next : I.Stage)
    (target : Record → Option ℚ) : Set (Record × input.StageSample next) :=
  {sample | ∃ p : ℚ, target sample.1 = some p ∧ sample.2 ∈ fixedPosteriorError input next p}

def selectedPosteriorOverflow (input : StatisticalInput I) (next : I.Stage)
    (target : Record → Option ℚ) (quota : ℕ) : Set (Record × input.StageSample next) :=
  {sample | ∃ p : ℚ, target sample.1 = some p ∧ sample.2 ∈ fixedPosteriorOverflow input next p quota}

noncomputable def selectedTargetBound (target : Record → Option ℚ) (record : Record) : ℝ≥0∞ :=
  match target record with
  | none => 0
  | some p => ENNReal.ofReal (p : ℝ)

theorem measurable_selectedTargetBound (target : Record → Option ℚ) (htarget : Measurable target) :
    Measurable (selectedTargetBound target) := by
  let value : Option ℚ → ℝ≥0∞ := fun p => match p with
    | none => 0
    | some p => ENNReal.ofReal (p : ℝ)
  exact (measurable_of_countable value).comp htarget

theorem measurableSet_selectedPosteriorError (input : StatisticalInput I) (next : I.Stage)
    (target : Record → Option ℚ) (htarget : Measurable target) :
    MeasurableSet (selectedPosteriorError input next target) := by
  have heq : selectedPosteriorError input next target =
      ⋃ p : ℚ, (target ⁻¹' {some p}) ×ˢ fixedPosteriorError input next p := by
    ext sample
    simp only [selectedPosteriorError, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod,
      Set.mem_preimage, Set.mem_singleton_iff]
  rw [heq]
  exact MeasurableSet.iUnion fun p => (htarget (measurableSet_singleton (some p))).prod
    (measurableSet_fixedPosteriorError input next p)

theorem measurableSet_selectedPosteriorOverflow (input : StatisticalInput I) (next : I.Stage)
    (target : Record → Option ℚ) (htarget : Measurable target) (quota : ℕ) :
    MeasurableSet (selectedPosteriorOverflow input next target quota) := by
  have heq : selectedPosteriorOverflow input next target quota =
      ⋃ p : ℚ, (target ⁻¹' {some p}) ×ˢ fixedPosteriorOverflow input next p quota := by
    ext sample
    simp only [selectedPosteriorOverflow, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod,
      Set.mem_preimage, Set.mem_singleton_iff]
  rw [heq]
  exact MeasurableSet.iUnion fun p => (htarget (measurableSet_singleton (some p))).prod
    (measurableSet_fixedPosteriorOverflow input next p quota)

omit [MeasurableSpace Record] in
theorem selectedPosteriorError_section_none (input : StatisticalInput I) (next : I.Stage)
    (target : Record → Option ℚ) (record : Record) (hnone : target record = none) :
    Prod.mk record ⁻¹' selectedPosteriorError input next target = ∅ := by
  ext sample
  simp [selectedPosteriorError, hnone]

omit [MeasurableSpace Record] in
theorem selectedPosteriorError_section_some (input : StatisticalInput I) (next : I.Stage)
    (target : Record → Option ℚ) (record : Record) (p : ℚ) (hsome : target record = some p) :
    Prod.mk record ⁻¹' selectedPosteriorError input next target = fixedPosteriorError input next p := by
  ext sample
  simp [selectedPosteriorError, hsome]

omit [MeasurableSpace Record] in
theorem selectedPosteriorOverflow_section_none (input : StatisticalInput I) (next : I.Stage)
    (target : Record → Option ℚ) (record : Record) (hnone : target record = none) (quota : ℕ) :
    Prod.mk record ⁻¹' selectedPosteriorOverflow input next target quota = ∅ := by
  ext sample
  simp [selectedPosteriorOverflow, hnone]

omit [MeasurableSpace Record] in
theorem selectedPosteriorOverflow_section_some (input : StatisticalInput I) (next : I.Stage)
    (target : Record → Option ℚ) (record : Record) (p : ℚ) (hsome : target record = some p) (quota : ℕ) :
    Prod.mk record ⁻¹' selectedPosteriorOverflow input next target quota = fixedPosteriorOverflow input next p quota := by
  ext sample
  simp [selectedPosteriorOverflow, hsome]

/-- A measurable countable choice of targets gives an actual product-law
kernel bound; None has no error event and contributes zero to the integral. -/
theorem selectedPosteriorError_product_le (input : StatisticalInput I) (next : I.Stage)
    (μ : Measure Record) (target : Record → Option ℚ) (htarget : Measurable target)
    (hvalid : ∀ (record : Record) (p : ℚ), target record = some p → 0 < p ∧ p ≤ 1 / 4) :
    μ.prod (input.stageLaw next) (selectedPosteriorError input next target) ≤
      ∫⁻ record, selectedTargetBound target record ∂μ := by
  rw [Measure.prod_apply (measurableSet_selectedPosteriorError input next target htarget)]
  apply lintegral_mono
  intro record
  change input.stageLaw next (Prod.mk record ⁻¹' selectedPosteriorError input next target) ≤ selectedTargetBound target record
  cases h : target record with
  | none =>
    rw [selectedPosteriorError_section_none input next target record h]
    simp only [measure_empty, selectedTargetBound, h, le_refl]
  | some p =>
    rw [selectedPosteriorError_section_some input next target record p h]
    have hv := hvalid record p h
    simpa only [selectedTargetBound, h] using stageLaw_fixedPosteriorError_le input next p hv.1 hv.2

/-- The bound retains the full probability of the inactive/None event.
It neither conditions on entering nor on eventual success. -/
theorem selectedPosteriorOverflow_product_le (input : StatisticalInput I) (next : I.Stage)
    (μ : Measure Record) (target : Record → Option ℚ) (htarget : Measurable target)
    (hvalid : ∀ (record : Record) (p : ℚ), target record = some p → 0 < p ∧ p ≤ 1 / 4)
    (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N) (exponent : ℕ)
    (hqualifies : PaperProofs.Statistics.DyadicQualifies
      (2 * N * PaperProofs.Statistics.referenceQuotaConstant N) delta exponent)
    (hfloor : ∀ (record : Record) (p : ℚ), target record = some p →
      delta / (PaperProofs.Statistics.referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) :
    μ.prod (input.stageLaw next)
        (selectedPosteriorOverflow input next target ((input.experiment next).rationalQuota exponent)) ≤
      ENNReal.ofReal (delta / (2 * N)) * μ {record | target record ≠ none} := by
  have hactive : MeasurableSet {record | target record ≠ none} :=
    (htarget (measurableSet_singleton none)).compl
  rw [Measure.prod_apply (measurableSet_selectedPosteriorOverflow input next target htarget _)]
  calc
    _ ≤ ∫⁻ record, {record | target record ≠ none}.indicator
        (fun _record => ENNReal.ofReal (delta / (2 * N))) record ∂μ := by
      apply lintegral_mono
      intro record
      change input.stageLaw next (Prod.mk record ⁻¹'
        selectedPosteriorOverflow input next target ((input.experiment next).rationalQuota exponent)) ≤ _
      cases h : target record with
      | none =>
        rw [selectedPosteriorOverflow_section_none input next target record h]
        simp [h]
      | some p =>
        rw [selectedPosteriorOverflow_section_some input next target record p h]
        have hv := hvalid record p h
        have hactiveRecord : record ∈ {record | target record ≠ none} := by simp [h]
        rw [Set.indicator_of_mem hactiveRecord]
        exact stageLaw_fixedPosteriorOverflow_le input next p hv.1 hv.2 delta hdelta hsmall N hN exponent hqualifies (hfloor record p h)
    _ = _ := lintegral_indicator_const hactive _

end CountableTargets

section ActualEntry

variable {Seed : Type} [MeasurableSpace Seed]

/-- Only an actual entry makes a target choice. A further `none` chosen after
entry represents a branch with no posterior test. -/
def entryGatedTarget (choose : Seed × List (VisibleEvent I) → Option ℚ)
    (record : Seed × EntryHistory I) : Option ℚ :=
  match record.2 with
  | none => none
  | some history => choose (record.1, history)

theorem measurable_entryGatedTarget (choose : Seed × List (VisibleEvent I) → Option ℚ)
    (hchoose : Measurable choose) : Measurable (entryGatedTarget choose) := by
  apply measurable_from_prod_countable_left
  intro history
  cases history with
  | none => exact measurable_const
  | some history =>
    exact hchoose.comp (measurable_id.prodMk measurable_const)

omit [MeasurableSpace Seed] in
theorem entryGatedTarget_none (choose : Seed × List (VisibleEvent I) → Option ℚ) (seed : Seed) :
    entryGatedTarget choose (seed, none) = none := rfl

omit [MeasurableSpace Seed] in
theorem entryGatedTarget_some_iff (choose : Seed × List (VisibleEvent I) → Option ℚ)
    (record : Seed × EntryHistory I) (p : ℚ) :
    entryGatedTarget choose record = some p ↔
      ∃ history : List (VisibleEvent I), record.2 = some history ∧ choose (record.1, history) = some p := by
  rcases record with ⟨seed, history⟩
  cases history <;> simp [entryGatedTarget]

def entryPosteriorError (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (choose : Seed × List (VisibleEvent I) → Option ℚ) : Set (Seed × input.World) :=
  (fun sample => (entrySeedHistory input C mode accounting rule next sample, sample.2 next)) ⁻¹'
    selectedPosteriorError input next (entryGatedTarget choose)

def entryPosteriorOverflow (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (choose : Seed × List (VisibleEvent I) → Option ℚ) (quota : ℕ) : Set (Seed × input.World) :=
  (fun sample => (entrySeedHistory input C mode accounting rule next sample, sample.2 next)) ⁻¹'
    selectedPosteriorOverflow input next (entryGatedTarget choose) quota

theorem measurableSet_entryPosteriorError (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hrule : MeasurableRule rule) (next : I.Stage)
    (choose : Seed × List (VisibleEvent I) → Option ℚ) (hchoose : Measurable choose) :
    MeasurableSet (entryPosteriorError input C mode accounting rule next choose) :=
  (measurableSet_selectedPosteriorError input next (entryGatedTarget choose)
    (measurable_entryGatedTarget choose hchoose)).preimage
      ((measurable_entrySeedHistory input C mode accounting rule hrule next).prodMk
        ((measurable_pi_apply next).comp measurable_snd))

theorem measurableSet_entryPosteriorOverflow (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hrule : MeasurableRule rule) (next : I.Stage)
    (choose : Seed × List (VisibleEvent I) → Option ℚ) (hchoose : Measurable choose) (quota : ℕ) :
    MeasurableSet (entryPosteriorOverflow input C mode accounting rule next choose quota) :=
  (measurableSet_selectedPosteriorOverflow input next (entryGatedTarget choose)
    (measurable_entryGatedTarget choose hchoose) quota).preimage
      ((measurable_entrySeedHistory input C mode accounting rule hrule next).prodMk
        ((measurable_pi_apply next).comp measurable_snd))

omit [MeasurableSpace Seed] in
/-- The event is empty on paths that never enter this stage. -/
theorem entryPosteriorError_excludes_unentered (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (choose : Seed × List (VisibleEvent I) → Option ℚ) (sample : Seed × input.World)
    (hnone : entryHistory input C mode accounting rule next sample = none) :
    sample ∉ entryPosteriorError input C mode accounting rule next choose := by
  simp [entryPosteriorError, selectedPosteriorError, entryGatedTarget, entrySeedHistory, hnone]

omit [MeasurableSpace Seed] in
theorem entryPosteriorOverflow_excludes_unentered (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (next : I.Stage)
    (choose : Seed × List (VisibleEvent I) → Option ℚ) (quota : ℕ) (sample : Seed × input.World)
    (hnone : entryHistory input C mode accounting rule next sample = none) :
    sample ∉ entryPosteriorOverflow input C mode accounting rule next choose quota := by
  simp [entryPosteriorOverflow, selectedPosteriorOverflow, entryGatedTarget, entrySeedHistory, hnone]

/-- The target may use the whole actual entry history and private seed.
The right side integrates over all paths, including those that never enter. -/
theorem entryPosteriorError_le (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (next : I.Stage)
    (choose : Seed × List (VisibleEvent I) → Option ℚ) (hchoose : Measurable choose)
    (hvalid : ∀ (seed : Seed) (history : List (VisibleEvent I)) (p : ℚ),
      choose (seed, history) = some p → 0 < p ∧ p ≤ 1 / 4) :
    input.seededWorldLaw ν (entryPosteriorError input C mode accounting policy.rule next choose) ≤
      ∫⁻ sample, selectedTargetBound (entryGatedTarget choose)
        (entrySeedHistory input C mode accounting policy.rule next sample) ∂input.seededWorldLaw ν := by
  let target := entryGatedTarget choose
  have ht : Measurable target := measurable_entryGatedTarget choose hchoose
  have hr := measurable_entrySeedHistory input C mode accounting policy.rule policy.measurable_rule next
  have hn : Measurable (fun sample : Seed × input.World => sample.2 next) :=
    (measurable_pi_apply next).comp measurable_snd
  have hs := measurableSet_selectedPosteriorError input next target ht
  have hv (record : Seed × EntryHistory I) (p : ℚ) (h : target record = some p) : 0 < p ∧ p ≤ 1 / 4 := by
    obtain ⟨history, _, hh⟩ := (entryGatedTarget_some_iff choose record p).mp h
    exact hvalid record.1 history p hh
  calc
    _ = (input.seededWorldLaw ν).map (fun sample =>
        (entrySeedHistory input C mode accounting policy.rule next sample, sample.2 next))
          (selectedPosteriorError input next target) := (Measure.map_apply (hr.prodMk hn) hs).symm
    _ = ((input.seededWorldLaw ν).map (entrySeedHistory input C mode accounting policy.rule next)).prod
        (input.stageLaw next) (selectedPosteriorError input next target) := by
      rw [entrySeedHistory_jointLaw input C mode accounting policy ν next]
    _ ≤ ∫⁻ record, selectedTargetBound target record
        ∂(input.seededWorldLaw ν).map (entrySeedHistory input C mode accounting policy.rule next) :=
      selectedPosteriorError_product_le input next _ target ht hv
    _ = _ := lintegral_map (measurable_selectedTargetBound target ht) hr

/-- An unconditional overflow bound on the actual world, weighted by the
probability that this stage enters and selects a posterior test. This theorem
concerns the potential stage tape; identifying the interpreter's observations
with this test remains the reference-policy execution obligation. -/
theorem entryPosteriorOverflow_le (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (next : I.Stage)
    (choose : Seed × List (VisibleEvent I) → Option ℚ) (hchoose : Measurable choose)
    (hvalid : ∀ (seed : Seed) (history : List (VisibleEvent I)) (p : ℚ),
      choose (seed, history) = some p → 0 < p ∧ p ≤ 1 / 4)
    (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N) (exponent : ℕ)
    (hqualifies : PaperProofs.Statistics.DyadicQualifies
      (2 * N * PaperProofs.Statistics.referenceQuotaConstant N) delta exponent)
    (hfloor : ∀ (seed : Seed) (history : List (VisibleEvent I)) (p : ℚ),
      choose (seed, history) = some p →
        delta / (PaperProofs.Statistics.referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) :
    input.seededWorldLaw ν (entryPosteriorOverflow input C mode accounting policy.rule next choose
      ((input.experiment next).rationalQuota exponent)) ≤
      ENNReal.ofReal (delta / (2 * N)) * input.seededWorldLaw ν {sample |
        entryGatedTarget choose (entrySeedHistory input C mode accounting policy.rule next sample) ≠ none} := by
  let target := entryGatedTarget choose
  have ht : Measurable target := measurable_entryGatedTarget choose hchoose
  have hr := measurable_entrySeedHistory input C mode accounting policy.rule policy.measurable_rule next
  have hn : Measurable (fun sample : Seed × input.World => sample.2 next) :=
    (measurable_pi_apply next).comp measurable_snd
  have hs := measurableSet_selectedPosteriorOverflow input next target ht ((input.experiment next).rationalQuota exponent)
  have hv (record : Seed × EntryHistory I) (p : ℚ) (h : target record = some p) : 0 < p ∧ p ≤ 1 / 4 := by
    obtain ⟨history, _, hh⟩ := (entryGatedTarget_some_iff choose record p).mp h
    exact hvalid record.1 history p hh
  have hf (record : Seed × EntryHistory I) (p : ℚ) (h : target record = some p) :
      delta / (PaperProofs.Statistics.referenceQuotaConstant N : ℝ) ≤ (p : ℝ) := by
    obtain ⟨history, _, hh⟩ := (entryGatedTarget_some_iff choose record p).mp h
    exact hfloor record.1 history p hh
  have hactive : MeasurableSet {record | target record ≠ none} :=
    (ht (measurableSet_singleton none)).compl
  calc
    _ = (input.seededWorldLaw ν).map (fun sample =>
        (entrySeedHistory input C mode accounting policy.rule next sample, sample.2 next))
          (selectedPosteriorOverflow input next target ((input.experiment next).rationalQuota exponent)) :=
      (Measure.map_apply (hr.prodMk hn) hs).symm
    _ = ((input.seededWorldLaw ν).map (entrySeedHistory input C mode accounting policy.rule next)).prod
        (input.stageLaw next) (selectedPosteriorOverflow input next target ((input.experiment next).rationalQuota exponent)) := by
      rw [entrySeedHistory_jointLaw input C mode accounting policy ν next]
    _ ≤ ENNReal.ofReal (delta / (2 * N)) *
        (input.seededWorldLaw ν).map (entrySeedHistory input C mode accounting policy.rule next)
          {record | target record ≠ none} :=
      selectedPosteriorOverflow_product_le input next _ target ht hv delta hdelta hsmall N hN exponent hqualifies hf
    _ = _ := by rw [Measure.map_apply hr hactive]; rfl

/-- Dropping the active-entry weight preserves the original per-stage cap. -/
theorem entryPosteriorOverflow_le_cap (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (next : I.Stage)
    (choose : Seed × List (VisibleEvent I) → Option ℚ) (hchoose : Measurable choose)
    (hvalid : ∀ (seed : Seed) (history : List (VisibleEvent I)) (p : ℚ),
      choose (seed, history) = some p → 0 < p ∧ p ≤ 1 / 4)
    (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N) (exponent : ℕ)
    (hqualifies : PaperProofs.Statistics.DyadicQualifies
      (2 * N * PaperProofs.Statistics.referenceQuotaConstant N) delta exponent)
    (hfloor : ∀ (seed : Seed) (history : List (VisibleEvent I)) (p : ℚ),
      choose (seed, history) = some p →
        delta / (PaperProofs.Statistics.referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) :
    input.seededWorldLaw ν (entryPosteriorOverflow input C mode accounting policy.rule next choose
      ((input.experiment next).rationalQuota exponent)) ≤ ENNReal.ofReal (delta / (2 * N)) := by
  refine (entryPosteriorOverflow_le input C mode accounting policy ν next choose hchoose hvalid
    delta hdelta hsmall N hN exponent hqualifies hfloor).trans ?_
  calc
    _ ≤ ENNReal.ofReal (delta / (2 * N)) * 1 := mul_le_mul_of_nonneg_left prob_le_one zero_le
    _ = _ := mul_one _

/-- The actual path floor can use a smaller rational reference risk. Applying
the analytic estimate at that risk and the unchanged dyadic exponent bounds
the overflow by the original real-risk cap; no larger target floor is assumed. -/
theorem entryPosteriorOverflow_referenceRisk_le (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (next : I.Stage)
    (choose : Seed × List (VisibleEvent I) → Option ℚ) (hchoose : Measurable choose)
    (hvalid : ∀ (seed : Seed) (history : List (VisibleEvent I)) (p : ℚ),
      choose (seed, history) = some p → 0 < p ∧ p ≤ 1 / 4)
    (delta : ℝ) (hsmall : delta ≤ 1 / 2) (risk : ℚ) (hrisk : 0 < risk) (hriskDelta : (risk : ℝ) ≤ delta)
    (N : ℕ) (hN : 0 < N) (exponent : ℕ)
    (hqualifies : PaperProofs.Statistics.DyadicQualifies
      (2 * N * PaperProofs.Statistics.referenceQuotaConstant N) (risk : ℝ) exponent)
    (hfloor : ∀ (seed : Seed) (history : List (VisibleEvent I)) (p : ℚ),
      choose (seed, history) = some p →
        (risk : ℝ) / (PaperProofs.Statistics.referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) :
    input.seededWorldLaw ν (entryPosteriorOverflow input C mode accounting policy.rule next choose
      ((input.experiment next).rationalQuota exponent)) ≤ ENNReal.ofReal (delta / (2 * N)) := by
  have hriskReal : 0 < (risk : ℝ) := by exact_mod_cast hrisk
  refine (entryPosteriorOverflow_le_cap input C mode accounting policy ν next choose hchoose hvalid
    (risk : ℝ) hriskReal (hriskDelta.trans hsmall) N hN exponent hqualifies hfloor).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right hriskDelta (by positivity)

end ActualEntry

end PaperProofs.Common.Native
