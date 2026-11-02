module

public import PaperProofs.Common.ReferenceController
public import PaperProofs.Common.ReferenceControllerQuota
public import PaperProofs.Common.PenaltyAsymptotics

/-!
Concrete remaining reference-controller obligations from price-proofs.tex.
The policy below is the actual visible-history rule, not an existential
optimal-policy placeholder. Qualification includes the original interface's
H0 certificate for this selected controller; numeric quota/H tests alone do
not imply it for an arbitrary NormalAccounting. None of these performance
targets is a field of Native.Policy or the executable replay cache.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace PaperProofs.Common.Native

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

def referenceQuota (input : StatisticalInput I) (exponent : ℕ) : I.Stage → ℕ :=
  fun stage => (input.experiment stage).rationalQuota exponent

def referenceIdealPolicy (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) : Policy input C .uncapped accounting Unit :=
  referenceUncappedPolicy input C hearly accounting available budget none

def referenceBoundedPolicy (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ) :
    Policy input C .uncapped accounting Unit :=
  referenceUncappedPolicy input C hearly accounting available budget
    (some (referenceQuota input exponent))

/-- The same exponent as the original real delta; the executable budget is
within a factor two and never enlarges an original quota. -/
structure ReferenceRiskChoice (N : ℕ) (delta : ℝ) (exponent : ℕ) (budget : ℚ) : Prop where
  positive : 0 < budget
  small : budget ≤ 1 / 2
  factor_two : delta / 2 ≤ (budget : ℝ)
  conservative : (budget : ℝ) ≤ delta
  original_exponent : IsMinimalDyadicExponent (2 * N * referenceQuotaConstant N) delta exponent
  same_exponent : BinaryExperiment.quotaExponent budget N = exponent

theorem exists_referenceRiskChoice (N : ℕ) (hN : 0 < N) (delta : ℝ)
    (hd : 0 < delta) (hsmall : delta ≤ 1 / 2) (exponent : ℕ)
    (he : IsMinimalDyadicExponent (2 * N * referenceQuotaConstant N) delta exponent) :
    ∃ budget : ℚ, ReferenceRiskChoice N delta exponent budget := by
  obtain ⟨budget, hp, hs, hf, hc, heq, _⟩ :=
    exists_referenceRisk_same_exponent_targets delta hd hsmall N hN exponent he
  exact ⟨budget, hp, hs, hf, hc, he, BinaryExperiment.quotaExponent_eq_original budget hp N exponent heq⟩

/-- The original H0 assumption is for this controller, including unsuccessful
prefixes. It is not imposed on arbitrary comparison policies. -/
structure ReferenceOriginalQualification (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ) : Prop where
  stage_quota : ∀ stage, referenceQuota input exponent stage ≤ C.reviewQuota stage
  total_calls : C.normalCallBound + ∑ stage, referenceQuota input exponent stage +
    min I.stageCount I.toolCount ≤ C.totalCallCap
  normal_calls : NormalCallCertificate input C .uncapped accounting
    (referenceBoundedPolicy input C hearly accounting available budget exponent) C.normalCallBound

/-- Actual all-sample/all-prefix review bounds, not a field of a policy. -/
def ReferenceReviewBounds (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ),
    0 < budget → budget ≤ 1 / 2 →
      ReviewQuotaCertificate input C accounting
        (referenceBoundedPolicy input C hearly accounting available budget exponent).rule
        (referenceQuota input exponent)

theorem referenceReviewBounds (input : StatisticalInput I) : ReferenceReviewBounds input := by
  intro C hearly accounting available budget exponent _hp _hs
  exact referenceRule_reviewQuotaCertificate (Seed := Unit) input C hearly accounting available budget
    (referenceQuota input exponent)

/-- Full native implementation target under the original quota/H/H0, with
identical actual rules and paths; no native legality is assumed. -/
def ReferenceNativeImplementation (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ),
    0 < budget → budget ≤ 1 / 2 →
    ReferenceOriginalQualification input C hearly accounting available budget exponent →
      ∃ policy : Policy input C .native accounting Unit,
        policy.rule = (referenceBoundedPolicy input C hearly accounting available budget exponent).rule ∧
        ∀ sample n, run input C .native accounting policy.rule sample n =
          run input C .uncapped accounting
            (referenceBoundedPolicy input C hearly accounting available budget exponent).rule sample n

theorem referenceNativeImplementation_of_reviewBounds (input : StatisticalInput I)
    (hreview : ReferenceReviewBounds input) : ReferenceNativeImplementation input := by
  intro C hearly accounting available budget exponent hp hs hq
  let policy := referenceBoundedPolicy input C hearly accounting available budget exponent
  let reviews := hreview C hearly accounting available budget exponent hp hs
  let native := policy.enforceCaps input C accounting (referenceQuota input exponent)
    reviews hq.normal_calls hq.stage_quota hq.total_calls
  refine ⟨native, rfl, ?_⟩
  intro sample n
  exact enforceCaps_run_eq input C accounting policy (referenceQuota input exponent)
    reviews hq.normal_calls hq.stage_quota hq.total_calls sample n

/-- Concrete implementation under the original interface's H0 certificate,
with no remaining review-bound premise. This does not prove that the supplied
normal accounting has that qualification for an arbitrary numerical H0. -/
theorem referenceNativeImplementation (input : StatisticalInput I) : ReferenceNativeImplementation input :=
  referenceNativeImplementation_of_reviewBounds input (referenceReviewBounds input)

/-- An actual exhausted-quota review on one specific stage. -/
def referenceStageOverflow (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ) (stage : I.Stage) :
    Set (Unit × input.World) :=
  {sample | ∃ n : ℕ,
    let state := run input C .uncapped accounting
      (referenceIdealPolicy input C hearly accounting available budget).rule sample n
    state.halted = false ∧
    (referenceIdealPolicy input C hearly accounting available budget).rule () state.history = .review stage ∧
    (quota stage : ℕ∞) ≤ state.ledger.reviews stage}

/-- First overflow analysis uses the genuine ideal interpreter and an actual
review action. The finite comparison includes T=Q as a valid write. -/
def referenceOverflow (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ) : Set (Unit × input.World) :=
  {sample | ∃ (n : ℕ) (stage : I.Stage),
    let state := run input C .uncapped accounting
      (referenceIdealPolicy input C hearly accounting available budget).rule sample n
    state.halted = false ∧
    (referenceIdealPolicy input C hearly accounting available budget).rule () state.history = .review stage ∧
    (quota stage : ℕ∞) ≤ state.ledger.reviews stage}

/-- Pathwise same-tape truncation and the corresponding global risk bound.
All earlier actual correction payments and observations remain in the bill. -/
def ReferenceTruncationGuarantee (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ),
    0 < budget → budget ≤ 1 / 2 →
    let ideal := referenceIdealPolicy input C hearly accounting available budget
    let bounded := referenceBoundedPolicy input C hearly accounting available budget exponent
    (∀ sample, runActualBill input C .uncapped accounting bounded.rule sample ≤
      runActualBill input C .uncapped accounting ideal.rule sample) ∧
    (∀ sample, sample ∉ referenceOverflow input C hearly accounting available budget
      (referenceQuota input exponent) →
      ∀ n, run input C .uncapped accounting bounded.rule sample n =
        run input C .uncapped accounting ideal.rule sample n) ∧
    risk input C .uncapped accounting bounded.rule (Measure.dirac ()) ≤
      risk input C .uncapped accounting ideal.rule (Measure.dirac ()) +
        input.seededWorldLaw (Measure.dirac ())
          (referenceOverflow input C hearly accounting available budget (referenceQuota input exponent))

/-- The entire ideal-reference overflow event is bounded with the original
real delta and exponent, after the same-bin rational budget choice. -/
def ReferenceOverflowGuarantee (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (delta : ℝ) (exponent : ℕ) (budget : ℚ),
    0 < delta → delta ≤ 1 / 2 →
    ReferenceRiskChoice I.stageCount delta exponent budget →
      input.seededWorldLaw (Measure.dirac ())
        (referenceOverflow input C hearly accounting I.tools budget (referenceQuota input exponent)) ≤
          ENNReal.ofReal (delta / 2)

def referenceEntryChoice (input : StatisticalInput I) (budget : ℚ) :
    Unit × List (VisibleEvent I) → Option ℚ :=
  fun sample => referenceEntryTarget input budget sample.2

theorem measurable_referenceEntryChoice (input : StatisticalInput I) (budget : ℚ) :
    Measurable (referenceEntryChoice input budget) :=
  (measurable_referenceEntryTarget input budget).comp measurable_snd

/-- The exact missing path-to-test bridge: any actual ideal review at an
exhausted quota belongs to the potential first-exit event selected at that
stage's genuine entry history. No conditioning on future success occurs. -/
def ReferenceOverflowIdentification (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (budget : ℚ) (exponent : ℕ), 0 < budget → budget ≤ 1 / 2 →
    ∀ stage : I.Stage,
    referenceStageOverflow input C hearly accounting I.tools budget (referenceQuota input exponent) stage ⊆
      entryPosteriorOverflow input C .uncapped accounting
        (referenceIdealPolicy input C hearly accounting I.tools budget).rule stage
        (referenceEntryChoice input budget) (referenceQuota input exponent stage)

/-- Conditional actual-stage overflow, stated by multiplication rather than
division so null entry histories are included. Each truth and every genuine
entry history is quantified; the conditioning event never selects success. -/
def ReferenceConditionalOverflowGuarantee (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (delta : ℝ) (exponent : ℕ) (budget : ℚ),
    0 < delta → delta ≤ 1 / 2 →
    ReferenceRiskChoice I.stageCount delta exponent budget →
      ∀ (stage : I.Stage) (history : List (VisibleEvent I)) (truth : Bool),
        let ideal := referenceIdealPolicy input C hearly accounting I.tools budget
        let entered := {sample : Unit × input.World |
          entryHistory input C .uncapped accounting ideal.rule stage sample = some history ∧
          (sample.2 stage).1 = truth}
        input.seededWorldLaw (Measure.dirac ())
          (referenceStageOverflow input C hearly accounting I.tools budget (referenceQuota input exponent) stage ∩ entered) ≤
            ENNReal.ofReal (delta / (2 * I.stageCount)) * input.seededWorldLaw (Measure.dirac ()) entered

theorem reference_entry_overflow_bound (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (delta : ℝ) (hsmall : delta ≤ 1 / 2) (exponent : ℕ) (budget : ℚ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (hN : 0 < I.stageCount) (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ())
      (entryPosteriorOverflow input C .uncapped accounting
        (referenceIdealPolicy input C hearly accounting I.tools budget).rule stage
        (referenceEntryChoice input budget) (referenceQuota input exponent stage)) ≤
          ENNReal.ofReal (delta / (2 * I.stageCount)) := by
  have hminimal := BinaryExperiment.quotaExponent_minimal budget choice.positive I.stageCount
  rw [choice.same_exponent] at hminimal
  apply entryPosteriorOverflow_referenceRisk_le input C .uncapped accounting
    (referenceIdealPolicy input C hearly accounting I.tools budget) (Measure.dirac ()) stage
    (referenceEntryChoice input budget) (measurable_referenceEntryChoice input budget)
    (fun _ history p hp => (referenceEntryTarget_bounds input budget p choice.positive choice.small history hp).imp_right And.left)
    delta hsmall budget choice.positive choice.conservative I.stageCount hN exponent hminimal.2.1
  intro _ history p hp
  have hfloor := (referenceEntryTarget_bounds input budget p choice.positive choice.small history hp).2.2
  exact_mod_cast hfloor

/-- Exact first-round B19 package. The potential-entry kernel bound is proved
above; actual path identification and the per-history/truth conditional
assertion remain pending. -/
def ReferenceOverflowClaims (input : StatisticalInput I) : Prop :=
  ReferenceOverflowIdentification input ∧ ReferenceConditionalOverflowGuarantee input ∧
    ReferenceOverflowGuarantee input

theorem referenceOverflow_eq_iUnion (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ) :
    referenceOverflow input C hearly accounting available budget quota =
      ⋃ stage : I.Stage, referenceStageOverflow input C hearly accounting available budget quota stage := by
  ext sample
  simp only [referenceOverflow, referenceStageOverflow, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨n, stage, h⟩
    exact ⟨stage, n, h⟩
  · rintro ⟨stage, n, h⟩
    exact ⟨n, stage, h⟩

/-- Union-bound assembly from an independent path-to-test identification.
The stage kernel estimate above is already proved; actual identification
and the stronger per-entry conditional assertion remain explicit obligations. -/
theorem referenceOverflowGuarantee_of_identification (input : StatisticalInput I)
    (hid : ReferenceOverflowIdentification input) : ReferenceOverflowGuarantee input := by
  intro C hearly accounting delta exponent budget hd hsmall choice
  rw [referenceOverflow_eq_iUnion]
  by_cases hN : 0 < I.stageCount
  · calc
      _ ≤ ∑ stage : I.Stage, input.seededWorldLaw (Measure.dirac ())
          (referenceStageOverflow input C hearly accounting I.tools budget (referenceQuota input exponent) stage) :=
        measure_iUnion_fintype_le _ _
      _ ≤ ∑ _stage : I.Stage, ENNReal.ofReal (delta / (2 * I.stageCount)) := by
        apply Finset.sum_le_sum
        intro stage _
        exact (measure_mono (hid C hearly accounting budget exponent choice.positive choice.small stage)).trans
          (reference_entry_overflow_bound input C hearly accounting delta hsmall exponent budget choice hN stage)
      _ = ENNReal.ofReal (delta / 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Instance.Stage, Fintype.card_fin, nsmul_eq_mul]
        change (I.stageCount : ℝ≥0∞) * ENNReal.ofReal (delta / (2 * I.stageCount)) = _
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg I.stageCount)]
        congr 1
        have hNR : (I.stageCount : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        field_simp [hNR]
  · have : IsEmpty I.Stage := ⟨fun stage => by have hs := stage.isLt; change stage.val < I.stageCount at hs; omega⟩
    simp

/-- The fixed-input ideal reference cost law: actual correction charges are
included on every path. The scale is converted to ENNReal, never the policy
expectation to Real. There is no H0 or native-feasibility premise here. -/
def ReferenceCostAsymptotics (input : StatisticalInput I) : Prop :=
  ∀ (available : Finset I.Tool) (depth : ℕ),
    errorRank I.compatibility available = (depth : ℕ∞) →
    ∀ epsilon : ℝ, 0 < epsilon → ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
        ∀ (C : Contract I) (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I),
          expectedBill input C .uncapped accounting
            (referenceIdealPolicy input C hcurrent.1 accounting available budget).rule (Measure.dirac ()) ≤
              ENNReal.ofReal ((1 + epsilon) * input.orderedCoefficient available *
                iteratedLog depth (budget : ℝ)⁻¹)

/-- The actual bad continuation, run on the unchanged fresh suffix. A
maximizing child has exactly the original finite bad depth. Its full expected
variable bill, multiplied by the test target, is bounded as local r tends
to zero. This is the O(1) branch obligation in B:212--226, not a lower bound
on a difference of successor prices. -/
def ReferenceBadBranchCostBound (input : StatisticalInput I) : Prop :=
  ∀ (stage : I.Stage) (available : Finset I.Tool) (depth : ℕ), 1 ≤ depth →
    badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available = (depth : ℕ∞) →
    ∀ tool ∈ I.eligible stage ∩ available,
      errorRank (I.compatibility.drop (stage.val + 1)) (available.erase tool) = (depth : ℕ∞) →
      ∃ (bound cutoff : ℝ), 0 ≤ bound ∧ 0 < cutoff ∧
        ∀ localRisk : ℚ, 0 < localRisk → localRisk ≤ 1 / 4 → (localRisk : ℝ) < cutoff →
          let childInput := input.freshSuffix (stage.val + 1)
          let childBudget := 2 * controllerBadRisk localRisk (controllerTarget localRisk depth)
          ∀ (C : Contract (I.freshSuffix (stage.val + 1))) (hcurrent : C.IsCurrentAllocation)
            (accounting : NormalAccounting (I.freshSuffix (stage.val + 1))),
            ENNReal.ofReal (controllerTarget localRisk depth : ℝ) *
              expectedBill childInput C .uncapped accounting
                (referenceIdealPolicy childInput C hcurrent.1 accounting (available.erase tool) childBudget).rule
                (Measure.dirac ()) ≤ ENNReal.ofReal bound

/-- Both the leading-term and actual bad-branch obligations for B18. -/
def ReferenceCostClaims (input : StatisticalInput I) : Prop :=
  ReferenceCostAsymptotics input ∧ ReferenceBadBranchCostBound input

/-- Concrete risk assembly from three distinct pending ingredients. No
ingredient assumes the bounded controller's final delta-risk conclusion. -/
theorem referenceBounded_risk_of_guarantees (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (hreference : ReferenceRiskGuarantee input C accounting)
    (htruncation : ReferenceTruncationGuarantee input)
    (hoverflow : ReferenceOverflowGuarantee input)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (exponent : ℕ) (budget : ℚ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget) :
    risk input C .uncapped accounting
      (referenceBoundedPolicy input C hcurrent.1 accounting I.tools budget exponent).rule (Measure.dirac ()) ≤
        ENNReal.ofReal delta := by
  have hideal := hreference hcurrent I.tools budget choice.positive choice.small
  have htrunc := (htruncation C hcurrent.1 accounting I.tools budget exponent
    choice.positive choice.small).2.2
  have htail := hoverflow C hcurrent.1 accounting delta exponent budget hd hsmall choice
  have hhalf : ENNReal.ofReal ((budget : ℝ) / 2) ≤ ENNReal.ofReal (delta / 2) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right choice.conservative (by norm_num))
  calc
    _ ≤ ENNReal.ofReal (delta / 2) + ENNReal.ofReal (delta / 2) :=
      htrunc.trans (add_le_add (hideal.trans hhalf) htail)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ delta / 2) (by positivity : 0 ≤ delta / 2)]
      congr 1
      ring

/-- Conditional connection of actual ideal performance to the true full-policy
native infimum. It preserves every already-paid charge, permits infinity,
and requires the original controller H0 certificate before native legality. -/
theorem native_value_le_reference_ideal_of_guarantees (input : StatisticalInput I)
    (C : Contract I) (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (hreference : ReferenceRiskGuarantee input C accounting)
    (htruncation : ReferenceTruncationGuarantee input)
    (hoverflow : ReferenceOverflowGuarantee input)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (exponent : ℕ) (budget : ℚ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceOriginalQualification input C hcurrent.1 accounting I.tools budget exponent) :
    value input C .native accounting (ENNReal.ofReal delta) ≤
      expectedBill input C .uncapped accounting
        (referenceIdealPolicy input C hcurrent.1 accounting I.tools budget).rule (Measure.dirac ()) := by
  have hs := referenceBounded_risk_of_guarantees input C hcurrent accounting hreference htruncation hoverflow
    delta hd hsmall exponent budget choice
  have hv := native_value_le_certified_uncapped input C accounting
    (referenceBoundedPolicy input C hcurrent.1 accounting I.tools budget exponent)
    (referenceQuota input exponent)
    (referenceReviewBounds input C hcurrent.1 accounting I.tools budget exponent choice.positive choice.small)
    qualification.normal_calls qualification.stage_quota qualification.total_calls
    (Measure.dirac ()) (ENNReal.ofReal delta) hs
  exact hv.trans (lintegral_mono (htruncation C hcurrent.1 accounting I.tools budget exponent
    choice.positive choice.small).1)

end PaperProofs.Common.Native

namespace PaperProofs.Common

open PaperProofs.Statistics PaperProofs.Structure Native

/-- Matching native upper law, pointwise in the fixed graph/channels/prices.
The original certificate explicitly includes the selected controller's actual
normal calls; its mere numerical quota/H tests are insufficient. -/
def StatisticalInput.NativeUpperPriceLaw {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ depth : ℕ, errorRank I.compatibility I.tools = (depth : ℕ∞) →
    ∀ epsilon : ℝ, 0 < epsilon → ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ (delta : ℝ) (exponent : ℕ) (budget : ℚ),
        0 < delta → delta < cutoff → delta ≤ 1 / 2 →
        ReferenceRiskChoice I.stageCount delta exponent budget →
        ∀ (C : Contract I) (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I),
          ReferenceOriginalQualification input C hcurrent.1 accounting I.tools budget exponent →
            value input C .native accounting (ENNReal.ofReal delta) ≤
              ENNReal.ofReal ((1 + epsilon) * input.orderedCoefficient I.tools *
                iteratedLog depth delta⁻¹)

/-- The infinite-rank part includes an actual zero-observation native policy,
not only a bound on an abstract infimum. -/
def StatisticalInput.NativeInfiniteRankPriceLaw {I : Instance} (input : StatisticalInput I) : Prop :=
  errorRank I.compatibility I.tools = ⊤ →
    ∀ (C : Contract I) (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
      (budget : ℚ) (exponent : ℕ), 0 < budget → budget ≤ 1 / 2 →
      ReferenceOriginalQualification input C hcurrent.1 accounting I.tools budget exponent →
        ∃ policy : Policy input C .native accounting Unit,
          risk input C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
          expectedObservationBill input C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
          expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
            (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection

/-- Full B24 target. The lower comparison remains cap independent; the
upper half carries only the original implementation qualification above.
This is currently a statement package, not a theorem or a value definition. -/
def StatisticalInput.FixedGraphPriceLaw {I : Instance} (input : StatisticalInput I) : Prop :=
  input.NativeLowerPriceLaw ∧ input.NativeUpperPriceLaw ∧ input.NativeInfiniteRankPriceLaw ∧
    ∀ depth : ℕ, errorRank I.compatibility I.tools = (depth : ℕ∞) →
      0 < input.orderedCoefficient I.tools

end PaperProofs.Common
