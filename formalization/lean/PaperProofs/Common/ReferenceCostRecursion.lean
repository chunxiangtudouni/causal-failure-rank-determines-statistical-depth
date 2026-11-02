module

public import PaperProofs.Common.ReferenceTwoBranchCost

/-!
The remaining actual-run base and no-tool recurrence for the B18 suffix
induction. Costs remain ENNReal and all failed-path charges are retained.
These statements do not assume the asymptotic conclusion or termination.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics
open PaperProofs.Structure

variable {I : Instance}

theorem runRemainingObservationBill_terminal {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (first : ℕ)
    (hterminal : I.stageCount ≤ first) (sample : Seed × input.World) :
    runRemainingObservationBill input C mode accounting rule first sample = 0 := by
  classical
  unfold runRemainingObservationBill
  apply Finset.sum_eq_zero
  intro stage _
  have hstage : stage.val < I.stageCount := stage.isLt
  rw [ite_eq_right (by omega)]

/-- No-tool errors never enter the next stage. The actual surviving entry
has the original untouched tools and original half-budget good child. -/
theorem referenceNextEntryCostFunction_noTool_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (hkind : referenceAvailableRankCase I available first ∅ = some .noTool)
    (sample : Unit × input.World) :
    referenceNextEntryCostFunction input C accounting available budget nextStage sample ≤
      referenceFreshChildObservationCost input nextStage available (budget / 2) := by
  cases hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) nextStage sample with
  | none => simp only [referenceNextEntryCostFunction, hentry]; exact bot_le
  | some history =>
    obtain ⟨error, risk, _, hrisk, hstep, hused, _⟩ := referenceInitialNextEntry_children input C hearly accounting
      available budget hbudget hsmall first nextStage hfirst hnext .noTool hkind sample history hentry
    cases error with
    | true => cases hstep
    | false =>
      have hr : risk = budget / 2 / 2 := Option.some.inj hstep
      have hu : historyUsed history = ∅ := hused
      have htwo : 2 * (budget / 2 / 2) = budget / 2 := by ring
      simp only [referenceNextEntryCostFunction, hentry, referenceEntryFreshObservationCost, hrisk, hu, hr, htwo]
      change referenceFreshChildObservationCost input nextStage (available \ (∅ : Finset I.Tool)) (budget / 2) ≤ _
      rw [Finset.sdiff_empty]

theorem referenceExpectedObservationBill_noTool_le
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (hkind : referenceAvailableRankCase I available first ∅ = some .noTool) :
    expectedObservationBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      referenceEntryLocalObservationPrice input available budget first [] +
        referenceFreshChildObservationCost input nextStage available (budget / 2) := by
  let μ := input.seededWorldLaw (Measure.dirac ())
  have hfuture : (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
      (referenceRule input available budget none) nextStage.val sample ∂μ) ≤
        referenceFreshChildObservationCost input nextStage available (budget / 2) := by
    rw [← lintegral_referenceNextEntryCostFunction input C hcurrent accounting available budget hbudget hsmall nextStage]
    apply (lintegral_mono (referenceNextEntryCostFunction_noTool_le input C hcurrent.1 accounting available budget
      hbudget hsmall first nextStage hfirst hnext hkind)).trans
    simp only [lintegral_const, measure_univ, mul_one, le_refl]
  calc
    _ ≤ referenceEntryLocalObservationPrice input available budget first [] +
        (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
          (referenceRule input available budget none) nextStage.val sample ∂μ) := by
      rw [referenceRemainingObservationBill_eq_entryFreshCosts input C hcurrent accounting available budget hbudget hsmall nextStage]
      exact referenceExpectedObservationBill_le_initial_add_entryFreshCosts input C hcurrent accounting available budget
        hbudget hsmall first nextStage hfirst hnext
    _ ≤ _ := add_le_add le_rfl hfuture

/-- One actual stage has no remaining observation term after its local
test, regardless of whether its ordinary report succeeds or fails. -/
theorem referenceExpectedObservationBill_single_stage_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (hsize : I.stageCount = 1)
    (first : I.Stage) (hfirst : first.val = 0) :
    expectedObservationBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      referenceEntryLocalObservationPrice input available budget first [] := by
  classical
  have hlegal := referenceRule_uncapped_legal (Seed := Unit) input C hearly accounting available budget none
  rw [expectedObservationBill_eq_sum_stage input C .uncapped accounting _ hlegal
    (measurable_referenceRule input available budget none)]
  have heq (other : I.Stage) : other = first := by
    apply Fin.ext
    have ho : other.val < I.stageCount := other.isLt
    omega
  rw [Finset.sum_eq_single first (fun other _ hne => (hne (heq other)).elim) (by simp)]
  exact referenceInitialStageObservationBill_le_localPrice input C hearly accounting available budget hbudget hsmall first hfirst

theorem referenceExpectedObservationBill_empty
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hsize : I.stageCount = 0) :
    expectedObservationBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) = 0 := by
  have : IsEmpty I.Stage := ⟨fun stage => by have hs : stage.val < I.stageCount := stage.isLt; omega⟩
  rw [expectedObservationBill_eq_sum_stage input C .uncapped accounting _
    (referenceRule_uncapped_legal (Seed := Unit) input C hearly accounting available budget none)
    (measurable_referenceRule input available budget none)]
  simp

theorem referenceExpectedBill_empty
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hsize : I.stageCount = 0) :
    expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) = 0 := by
  have hbound := expectedBill_le_observation_add input C .uncapped accounting
    (referenceIdealPolicy input C hearly accounting available budget) (Measure.dirac ())
  change expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
    expectedObservationBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) + _ at hbound
  rw [referenceExpectedObservationBill_empty input C hearly accounting available budget hsize, hsize,
    Nat.zero_min, Nat.cast_zero, zero_mul, zero_add] at hbound
  exact le_antisymm hbound bot_le

private theorem singleton_compatibility (first : I.Stage) (hfirst : first.val = 0)
    (hsize : I.stageCount = 1) : I.compatibility = [I.eligible first] := by
  apply List.ext_getElem
  · change I.stageCount = 1
    exact hsize
  · intro index hleft hright
    have hi : index = 0 := by simpa only [List.length_singleton] using Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hright)
    subst index
    simp only [List.getElem_cons_zero]
    change I.compatibility[0] = I.compatibility[first.val]
    simp only [hfirst]

theorem reference_single_stage_finite_rank (first : I.Stage) (hfirst : first.val = 0)
    (hsize : I.stageCount = 1) (available : Finset I.Tool)
    (hfinite : errorRank I.compatibility available ≠ ⊤) :
    I.eligible first ∩ available = ∅ ∧ errorRank I.compatibility available = 1 := by
  have hsingle := singleton_compatibility first hfirst hsize
  have hempty : I.eligible first ∩ available = ∅ := by
    by_contra hn
    obtain ⟨tool, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hn
    have hmax : badChildRank (I.eligible first) [] available = ⊤ := by
      apply top_unique
      simpa only [errorRank_terminal] using childRank_le_badChildRank (I.eligible first) [] available ht
    apply hfinite
    rw [hsingle, errorRank_cons, errorRank_terminal, hmax]
    simp
  refine ⟨hempty, ?_⟩
  rw [hsingle, errorRank_cons, errorRank_terminal,
    (badChildRank_eq_zero_iff (I.eligible first) [] available).mpr hempty]
  simp

theorem reference_single_stage_coefficient (input : StatisticalInput I)
    (first : I.Stage) (hfirst : first.val = 0) (hsize : I.stageCount = 1)
    (available : Finset I.Tool) (hfinite : errorRank I.compatibility available ≠ ⊤) :
    input.orderedCoefficient available = (input.experiment first).coefficient := by
  obtain ⟨hempty, hrank⟩ := reference_single_stage_finite_rank first hfirst hsize available hfinite
  have hweighted : input.weightedSchedule = [(I.eligible first, (input.experiment first).coefficient)] := by
    apply List.ext_getElem
    · simpa only [StatisticalInput.weightedSchedule, List.length_ofFn, List.length_singleton, Instance.stageCount] using hsize
    · intro index hleft hright
      have hi : index = 0 := by simpa only [List.length_singleton] using Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hright)
      subst index
      simp only [StatisticalInput.weightedSchedule, List.getElem_ofFn, List.getElem_cons_zero]
      have heq : (⟨0, by have := first.isLt; omega⟩ : I.Stage) = first := Fin.ext hfirst.symm
      rw [heq]
  rw [StatisticalInput.orderedCoefficient, hweighted]
  have hrank' : errorRank [I.eligible first] available = 1 := by
    rw [← singleton_compatibility first hfirst hsize]
    exact hrank
  simp only [Statistics.orderedCoefficient, eligibilitySchedule, List.map_nil, hrank',
    ENat.one_ne_top, ite_false, errorRank_terminal]
  have hbad := (badChildRank_eq_zero_iff (I.eligible first) [] available).mpr hempty
  rw [hbad]
  simp

private theorem log_affine_cutoff (A : ℝ) (hA : 0 < A) (offset fee : ℝ)
    (hfee : 0 ≤ fee) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ risk : ℝ, 0 < risk → risk < cutoff →
      0 ≤ A * (Real.log risk⁻¹ + offset) ∧
        A * (Real.log risk⁻¹ + offset) + fee ≤ (1 + epsilon) * A * Real.log risk⁻¹ := by
  let M := |offset| + (fee + A * |offset|) / (epsilon * A) + 1
  have hden : 0 < epsilon * A := mul_pos hepsilon hA
  have hratio : 0 ≤ (fee + A * |offset|) / (epsilon * A) := by positivity
  refine ⟨Real.exp (-M), Real.exp_pos _, ?_⟩
  intro risk hrisk hsmall
  have hl : M < Real.log risk⁻¹ := by
    have h := Real.log_lt_log hrisk hsmall
    rw [Real.log_exp] at h
    rw [Real.log_inv]
    linarith
  have habs : |offset| ≤ Real.log risk⁻¹ := by dsimp [M] at hl; linarith
  have hthreshold : (fee + A * |offset|) / (epsilon * A) ≤ Real.log risk⁻¹ := by
    dsimp [M] at hl
    have hnonneg := abs_nonneg offset
    linarith
  have hpay : fee + A * |offset| ≤ Real.log risk⁻¹ * (epsilon * A) := (div_le_iff₀ hden).mp hthreshold
  have hterm : A * offset ≤ A * |offset| := mul_le_mul_of_nonneg_left (le_abs_self offset) hA.le
  have hpositive : 0 ≤ Real.log risk⁻¹ + offset := by have := neg_abs_le offset; linarith
  exact ⟨mul_nonneg hA.le hpositive, by nlinarith⟩

/-- The complete ORIGINAL B18 leading-cost target for the one-stage
induction base. The cutoff is uniform in contracts and normal accounting;
all actual correction fees remain, and no finite-cost premise is added. -/
theorem referenceCostAsymptotics_single_stage (input : StatisticalInput I)
    (hsize : I.stageCount = 1) : ReferenceCostAsymptotics input := by
  intro available depth hrank epsilon hepsilon
  let first : I.Stage := ⟨0, by change 0 < I.stageCount; omega⟩
  have hfirst : first.val = 0 := rfl
  have hfinite : errorRank I.compatibility available ≠ ⊤ := by
    rw [hrank]
    exact ENat.natCast_ne_top depth
  have hrankOne := (reference_single_stage_finite_rank first hfirst hsize available hfinite).2
  have hd : depth = 1 := ENat.natCast_inj.mp (hrank.symm.trans hrankOne)
  subst depth
  let E := input.experiment first
  let offset := Real.log (referenceQuotaConstant I.stageCount : ℝ) + E.logIncrementBound true +
    2 * |Real.log (E.priorReal true / E.priorReal false)|
  let fee : ℝ≥0∞ := (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection
  have hfee : fee ≠ ⊤ := ENNReal.mul_ne_top (by finiteness) input.fees.maxCorrection_lt_top.ne
  obtain ⟨cutoff, hcutoff, hscalar⟩ := log_affine_cutoff E.coefficient E.coefficient_pos offset fee.toReal
    ENNReal.toReal_nonneg epsilon hepsilon
  refine ⟨cutoff, hcutoff, ?_⟩
  intro budget hbudget hsmall hcut C hcurrent accounting
  have hb : (0 : ℝ) < (budget : ℝ) := by exact_mod_cast hbudget
  have hs := hscalar (budget : ℝ) hb hcut
  have hbound := referenceExpectedBill_le_global_add_corrections input C hcurrent.1 accounting available budget hbudget hsmall
  have heq (other : I.Stage) : other = first := by
    apply Fin.ext
    have ho : other.val < I.stageCount := other.isLt
    omega
  rw [Finset.sum_eq_single first (fun other _ hne => (hne (heq other)).elim) (by simp)] at hbound
  change expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
    ENNReal.ofReal (E.coefficient * (Real.log ((referenceQuotaConstant I.stageCount : ℝ) / (budget : ℝ)) +
      E.logIncrementBound true + 2 * |Real.log (E.priorReal true / E.priorReal false)|)) + fee at hbound
  have hC : (0 : ℝ) < (referenceQuotaConstant I.stageCount : ℝ) := by
    unfold referenceQuotaConstant
    positivity
  have hoffset : Real.log ((referenceQuotaConstant I.stageCount : ℝ) / (budget : ℝ)) +
      E.logIncrementBound true + 2 * |Real.log (E.priorReal true / E.priorReal false)| =
        Real.log (budget : ℝ)⁻¹ + offset := by
    rw [Real.log_div hC.ne' hb.ne', Real.log_inv]
    dsimp [offset]
    ring
  rw [hoffset] at hbound
  have hcoefficient := reference_single_stage_coefficient input first hfirst hsize available hfinite
  calc
    _ ≤ ENNReal.ofReal (E.coefficient * (Real.log (budget : ℝ)⁻¹ + offset)) + fee := hbound
    _ = ENNReal.ofReal (E.coefficient * (Real.log (budget : ℝ)⁻¹ + offset) + fee.toReal) := by
      rw [ENNReal.ofReal_add hs.1 ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfee]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by simpa only [hcoefficient, iteratedLog] using hs.2)

theorem referenceCostAsymptotics_empty (input : StatisticalInput I)
    (hsize : I.stageCount = 0) : ReferenceCostAsymptotics input := by
  intro available depth hrank
  have hnil : I.compatibility = [] := List.length_eq_zero_iff.mp hsize
  rw [hnil, errorRank_terminal] at hrank
  exact (ENat.top_ne_natCast depth hrank).elim

theorem referenceBadBranchCostBound_atMostOne (input : StatisticalInput I)
    (hsize : I.stageCount ≤ 1) : ReferenceBadBranchCostBound input := by
  intro stage available depth _ _ tool _ hrank
  have hdrop : I.compatibility.drop (stage.val + 1) = [] := by
    apply List.drop_eq_nil_iff.mpr
    change I.stageCount ≤ stage.val + 1
    omega
  rw [hdrop, errorRank_terminal] at hrank
  exact (ENat.top_ne_natCast depth hrank).elim

/-- Both original B18 obligations are proved for the zero/one-stage base.
The positive finite bad-child obligation is empty because every such child
is terminal and has independently defined infinite game rank. -/
theorem referenceCostClaims_atMostOne (input : StatisticalInput I)
    (hsize : I.stageCount ≤ 1) : ReferenceCostClaims input := by
  refine ⟨?_, referenceBadBranchCostBound_atMostOne input hsize⟩
  by_cases hz : I.stageCount = 0
  · exact referenceCostAsymptotics_empty input hz
  · exact referenceCostAsymptotics_single_stage input (by omega)

end PaperProofs.Common.Native
