module

public import PaperProofs.Retained.PRet_RetainedGuard_007
public import PaperProofs.Retained.Game
public import PaperProofs.Retained.Terminal
public import PaperProofs.Common.ReferenceCertification
public import PaperProofs.Common.HealthyValue
public import Mathlib.Data.List.Sections
public import Mathlib.Data.List.MinMax

/-! Concrete retained upper script and independent retained comparison
objects for frozen price-proofs.tex:313--341. No efficient general matching
or girth oracle is assumed: the selector and rank query enumerate finite
sets. Statistical performance, rearrangement and original-cap correctness
remain separate propositions, never controller or healthy-state fields. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PaperProofs.Retained

open Common Common.Native Statistics

universe u

def pastStages (I : Instance) (next : ℕ) : Finset I.Stage := Finset.univ.filter (fun i => i.val < next)

def Healthy (I : Instance) (next : ℕ) (errors : Finset I.Stage) : Prop :=
  next ≤ I.stageCount ∧ errors ⊆ pastStages I next ∧ Matchable I errors

instance healthy_decidable (I : Instance) (next : ℕ) (errors : Finset I.Stage) : Decidable (Healthy I next errors) := by
  unfold Healthy pastStages
  infer_instance

theorem healthy_initial (I : Instance) : Healthy I 0 ∅ :=
  ⟨Nat.zero_le _, Finset.empty_subset _, matchable_empty I⟩

theorem healthy_current_not_mem (I : Instance) (stage : I.Stage) (errors : Finset I.Stage)
    (healthy : Healthy I stage.val errors) : stage ∉ errors := by
  intro hstage
  exact (Nat.lt_irrefl stage.val) (Finset.mem_filter.mp (healthy.2.1 hstage)).2

theorem healthy_correct (I : Instance) (stage : I.Stage) (errors : Finset I.Stage)
    (healthy : Healthy I stage.val errors) : Healthy I (stage.val + 1) errors := by
  refine ⟨Nat.succ_le_of_lt stage.isLt, ?_, healthy.2.2⟩
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
    Nat.lt_succ_of_lt (Finset.mem_filter.mp (healthy.2.1 hi)).2⟩

theorem healthy_error_iff (I : Instance) (stage : I.Stage) (errors : Finset I.Stage)
    (healthy : Healthy I stage.val errors) :
    Healthy I (stage.val + 1) (insert stage errors) ↔ Matchable I (insert stage errors) := by
  constructor
  · exact fun h => h.2.2
  · intro hmatch
    refine ⟨Nat.succ_le_of_lt stage.isLt, ?_, hmatch⟩
    exact Finset.insert_subset_iff.mpr ⟨
      Finset.mem_filter.mpr ⟨Finset.mem_univ stage, Nat.lt_succ_self stage.val⟩,
      (healthy_correct I stage errors healthy).2.1⟩

/-- Once a retained error set is dependent, adding future errors cannot repair
it. This statement concerns matching, independently of any native controller. -/
theorem healthy_error_permanent (I : Instance) (stage : I.Stage) (errors : Finset I.Stage)
    (hbad : ¬ Matchable I (insert stage errors)) (future : Finset I.Stage) :
    ¬ Matchable I (insert stage errors ∪ future) := by
  intro hmatch
  exact hbad (hmatch.subset Finset.subset_union_left)

theorem healthy_play_correct (I : Instance) (stage : I.Stage) (old errors : Finset I.Stage)
    (count : ℕ) (success : Bool) (healthy : Healthy I stage.val old)
    (continuation : Play I (stagesFrom I (stage.val + 1)) old errors count success) :
    Play I (stagesFrom I stage.val) old errors count success := by
  rw [stagesFrom_cons I stage]
  exact .correct healthy.2.2 continuation

theorem healthy_play_error (I : Instance) (stage : I.Stage) (old errors : Finset I.Stage)
    (count : ℕ) (success : Bool) (healthy : Healthy I stage.val old)
    (continuation : Play I (stagesFrom I (stage.val + 1)) (insert stage old) errors count success) :
    Play I (stagesFrom I stage.val) old (insert stage errors) (count + 1) success := by
  rw [stagesFrom_cons I stage]
  exact .error healthy.2.2 continuation

theorem healthy_play_error_failure (I : Instance) (stage : I.Stage) (old : Finset I.Stage)
    (healthy : Healthy I stage.val old) (hbad : ¬ Matchable I (insert stage old)) :
    Play I (stagesFrom I stage.val) old {stage} 1 false := by
  simpa using healthy_play_error I stage old ∅ 0 false healthy
    (.failed (stagesFrom I (stage.val + 1)) (insert stage old) hbad)

/-- R02's healthy-state graph is tied to the original finite-stage Play:
correct declarations keep H; errors insert the current stage, with immediate
and permanent failure precisely when the enlarged set is unmatchable. -/
def HealthyStepClaims (I : Instance) : Prop :=
  (∀ (stage : I.Stage) (old : Finset I.Stage), Healthy I stage.val old →
    stage ∉ old ∧ Healthy I (stage.val + 1) old ∧
      (Healthy I (stage.val + 1) (insert stage old) ↔ Matchable I (insert stage old))) ∧
  (∀ (stage : I.Stage) (old : Finset I.Stage), Healthy I stage.val old →
    ¬ Matchable I (insert stage old) →
      Play I (stagesFrom I stage.val) old {stage} 1 false ∧
        ∀ future : Finset I.Stage, ¬ Matchable I (insert stage old ∪ future)) ∧
  (∀ (stage : I.Stage) (old errors : Finset I.Stage) (count : ℕ) (success : Bool),
    Healthy I stage.val old →
      Play I (stagesFrom I (stage.val + 1)) old errors count success →
        Play I (stagesFrom I stage.val) old errors count success) ∧
  (∀ (stage : I.Stage) (old errors : Finset I.Stage) (count : ℕ) (success : Bool),
    Healthy I stage.val old →
      Play I (stagesFrom I (stage.val + 1)) (insert stage old) errors count success →
        Play I (stagesFrom I stage.val) old (insert stage errors) (count + 1) success)

theorem healthyStepClaims (I : Instance) : HealthyStepClaims I := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro stage old healthy
    exact ⟨healthy_current_not_mem I stage old healthy, healthy_correct I stage old healthy,
      healthy_error_iff I stage old healthy⟩
  · intro stage old healthy hbad
    exact ⟨healthy_play_error_failure I stage old healthy hbad,
      healthy_error_permanent I stage old hbad⟩
  · exact healthy_play_correct I
  · exact healthy_play_error I

def reportedError {I : Instance} (history : List (VisibleEvent I)) (stage : I.Stage) : Option Bool := do
  let written ← historyWrite history stage
  let reported ← historyReport history stage
  if written.2 = reported.2 then some (written.1 != reported.1) else none

def reportedErrors (I : Instance) (history : List (VisibleEvent I)) (next : ℕ) : Finset I.Stage :=
  Finset.univ.filter (fun i => i.val < next ∧ reportedError history i = some true)

def assignmentCandidates (I : Instance) : List (List (Option I.Tool)) :=
  (List.ofFn (fun _stage : I.Stage => none :: (List.finRange I.toolCount).map some)).sections

def AssignmentValid (I : Instance) (errors : Finset I.Stage) (candidate : List (Option I.Tool)) : Prop :=
  candidate.length = I.stageCount ∧
  (∀ i : I.Stage, if i ∈ errors then ∃ tool, candidate[i.val]?.join = some tool ∧ tool ∈ I.eligible i
    else candidate[i.val]?.join = none) ∧
  ∀ (i j : I.Stage) (tool : I.Tool), candidate[i.val]?.join = some tool →
    candidate[j.val]?.join = some tool → i = j

instance assignmentValid_decidable (I : Instance) (errors : Finset I.Stage) (candidate : List (Option I.Tool)) :
    Decidable (AssignmentValid I errors candidate) := by
  unfold AssignmentValid
  infer_instance

/-- First feasible distinct-compatible matching. It minimizes NO fee.
The analysis rearrangement below instead preserves the old paid pairs. -/
def firstAssignment (I : Instance) (errors : Finset I.Stage) : Option (List (Option I.Tool)) :=
  (assignmentCandidates I).find? (fun candidate => decide (AssignmentValid I errors candidate))

def TerminalAssignmentCorrect (I : Instance) : Prop :=
  (∀ errors candidate, firstAssignment I errors = some candidate → AssignmentValid I errors candidate) ∧
    ∀ errors, Matchable I errors ↔ (firstAssignment I errors).isSome = true

/-- A finite search over the original future error sets. none means no
unsafe budget; some 0 means the current set itself is already dependent. -/
def unsafeBudget (I : Instance) (next : ℕ) (errors : Finset I.Stage) (budget : ℕ) : Bool :=
  decide (∃ future ∈ (stagesFrom I next).toFinset.powerset,
    future.card ≤ budget ∧ ¬ Matchable I (errors ∪ future))

def rankIndex (I : Instance) (next : ℕ) (errors : Finset I.Stage) : Option ℕ :=
  (List.range (I.stageCount + 1)).find? (unsafeBudget I next errors)

def rankCase (I : Instance) (stage : I.Stage) (errors : Finset I.Stage) : Option ReferenceBudgetCase :=
  match rankIndex I stage.val errors with
  | none => some .infiniteRank
  | some _ => if ¬ Matchable I (insert stage errors) then some .noTool else
      match rankIndex I (stage.val + 1) (insert stage errors) with
      | none => none
      | some depth => if h : 0 < depth then some (.finiteBad ⟨depth, h⟩) else none

structure BudgetCache (I : Instance) where
  errors : Finset I.Stage
  risk : ℚ

def replayBudgetStep (I : Instance) (history : List (VisibleEvent I))
    (cache : BudgetCache I) (stage : I.Stage) : Option (BudgetCache I) := do
  let error ← reportedError history stage
  let kind ← rankCase I stage cache.errors
  let child ← referenceBudgetStep kind error cache.risk
  let errors := if error then insert stage cache.errors else cache.errors
  if Matchable I errors then some ⟨errors, child⟩ else none

def replayBudget (I : Instance) (budget : ℚ) (history : List (VisibleEvent I)) (next : ℕ) : Option (BudgetCache I) :=
  ((List.finRange I.stageCount).take next).foldlM (replayBudgetStep I history) ⟨∅, budget / 2⟩

def retainedTestingAction {I : Instance} (input : StatisticalInput I) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (cache : BudgetCache I) (stage : I.Stage) : Action I :=
  match rankCase I stage cache.errors with
  | none => .abandon
  | some .infiniteRank => .write stage false
  | some .noTool | some (.finiteBad _) =>
      match (rankCase I stage cache.errors).bind (fun kind => referenceBudgetTarget kind cache.risk) with
      | none => .abandon
      | some target =>
          if hv : ∀ symbol ∈ historyObservations history stage, symbol < (input.experiment stage).alphabetSize then
            let word := historyObservationWord input history stage hv
            if (input.experiment stage).rationalWordHits target word then .write stage ((input.experiment stage).rationalWordMAP word)
            else match limit with
            | none => .review stage
            | some quota => if (historyObservations history stage).length < quota stage then .review stage else .abandon
          else .abandon

def terminalMatchingAction (I : Instance) (history : List (VisibleEvent I)) : Action I :=
  let errors := reportedErrors I history I.stageCount
  match firstAssignment I errors with
  | none => .abandon
  | some assignment =>
      match (List.finRange I.stageCount).find? (fun stage =>
        decide (stage ∈ errors) && !((historyExecutions history).any (fun e => e.1.stage == stage))) with
      | none => .stop
      | some stage =>
          match assignment[stage.val]?.join, referenceVisibleHandle history stage with
          | some tool, some handle =>
              match (historyCommitments history).find? (fun a => a.1.stage == stage) with
              | none => .allocate handle tool
              | some old => if old.2 = tool then .execute handle tool else .abandon
          | _, _ => .abandon

def retainedCandidate {I : Instance} (input : StatisticalInput I) (budget : ℚ)
    (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I)) : Action I :=
  if historyHalted history then .stop else
  if hstage : historyCursor history < I.stageCount then
    let stage : I.Stage := ⟨historyCursor history, hstage⟩
    match replayBudget I budget history stage.val with
    | none => .abandon
    | some cache =>
        if ¬ Healthy I stage.val cache.errors ∨ ¬ (0 < cache.risk ∧ cache.risk ≤ 1 / 4) then .abandon else
        match historyWrite history stage with
        | none => retainedTestingAction input limit history cache stage
        | some _ => match reportedError history stage with
          | none => .abandon
          | some error => if Matchable I (if error then insert stage cache.errors else cache.errors) then .advance stage else .abandon
  else if historyCursor history = I.stageCount then terminalMatchingAction I history else .abandon

def retainedRule {I : Instance} (input : StatisticalInput I) (budget : ℚ)
    (limit : ReferenceObservationLimit I) : PolicyRule I Unit :=
  PRetRetainedGuard007.guarded
    (fun _ history => retainedCandidate input budget limit history)

theorem retainedRule_uncapped_legal {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I) :
    LegalRule input C .uncapped accounting (retainedRule input budget limit) := by
  exact PRetRetainedGuard007.guarded_legal input C hretained accounting
    (fun (_ : Unit) history => retainedCandidate input budget limit history)

def retainedPolicy {I : Instance} (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I) :
    Policy input C .uncapped accounting Unit where
  rule := retainedRule input budget limit
  measurable_rule := measurable_of_countable _
  legal := retainedRule_uncapped_legal input C hretained accounting budget limit

def idealPolicy {I : Instance} (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) : Policy input C .uncapped accounting Unit :=
  retainedPolicy input C hretained accounting budget none

def boundedPolicy {I : Instance} (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (exponent : ℕ) : Policy input C .uncapped accounting Unit :=
  retainedPolicy input C hretained accounting budget (some (referenceQuota input exponent))

structure OriginalQualification {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (budget : ℚ) (exponent : ℕ) : Prop where
  stage_quota : ∀ i, referenceQuota input exponent i ≤ C.reviewQuota i
  total_calls : C.normalCallBound + ∑ i, referenceQuota input exponent i + min I.stageCount I.toolCount ≤ C.totalCallCap
  normal_calls : NormalCallCertificate input C .uncapped accounting (boundedPolicy input C hretained accounting budget exponent) C.normalCallBound

/-- The independent first-failure comparator keeps the original tools and
ALL future visible-history policies. Only its terminal success test relaxes
actual commitments to joint matchability with the already known old H. -/
def freshContract (I : Instance) : Contract I :=
  ⟨.early, .terminalBarrier, .terminalBarrier, fun _ => 0, 0, 0⟩

def liftedErrors (I : Instance) (next : ℕ) (L : Ledger (I.freshSuffix next)) : Finset I.Stage :=
  (ordinaryMismatches L).image (I.freshStageLift next)

section FreshPolicy

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

def freshSuccess (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (rule : PolicyRule (I.freshSuffix next) Seed) (sample : Seed × (input.freshSuffix next).World) : Prop :=
  ∃ n,
    let state := run (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)) rule sample n
    state.halted = true ∧ state.ledger.finished = true ∧ state.ledger.abandoned = false ∧
      Matchable I (old ∪ liftedErrors I next state.ledger)

theorem measurableSet_freshSuccess (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (rule : PolicyRule (I.freshSuffix next) Seed) (hm : MeasurableRule rule) :
    MeasurableSet {sample | freshSuccess input next old rule sample} := by
  have hset (n : ℕ) : MeasurableSet {sample : Seed × (input.freshSuffix next).World |
      let state := run (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
        (zeroNormalAccounting (I.freshSuffix next)) rule sample n
      state.halted = true ∧ state.ledger.finished = true ∧ state.ledger.abandoned = false ∧
        Matchable I (old ∪ liftedErrors I next state.ledger)} :=
    (measurable_run (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)) rule hm n) (MeasurableSpace.measurableSet_top (s :=
        {state : State (I.freshSuffix next) | state.halted = true ∧ state.ledger.finished = true ∧
          state.ledger.abandoned = false ∧ Matchable I (old ∪ liftedErrors I next state.ledger)}))
  have heq : {sample | freshSuccess input next old rule sample} =
      ⋃ n : ℕ, {sample : Seed × (input.freshSuffix next).World |
        let state := run (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
          (zeroNormalAccounting (I.freshSuffix next)) rule sample n
        state.halted = true ∧ state.ledger.finished = true ∧ state.ledger.abandoned = false ∧
          Matchable I (old ∪ liftedErrors I next state.ledger)} := by
    ext sample
    simp only [freshSuccess, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion hset

noncomputable def freshRisk (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (rule : PolicyRule (I.freshSuffix next) Seed) (ν : Measure Seed) : ℝ≥0∞ :=
  (input.freshSuffix next).seededWorldLaw ν {sample | ¬ freshSuccess input next old rule sample}

noncomputable def freshObjective (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (rule : PolicyRule (I.freshSuffix next) Seed) (ν : Measure Seed) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  expectedObservationBill (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
    (zeroNormalAccounting (I.freshSuffix next)) rule ν + penalty * freshRisk input next old rule ν

/-- H is retained in the actual success predicate; this is not the current
allocation available-tool suffix value and is not a Bellman definition. -/
noncomputable def freshPenalty (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (SmallSeed : Type), ⨅ (m : MeasurableSpace SmallSeed),
    letI : MeasurableSpace SmallSeed := m
    ⨅ (ν : Measure SmallSeed) (_h : IsProbabilityMeasure ν),
      ⨅ policy : Policy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
        (zeroNormalAccounting (I.freshSuffix next)) SmallSeed,
        freshObjective input next old policy.rule ν penalty

theorem freshPenalty_le_policy (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (penalty : ℝ≥0∞) {SmallSeed : Type} [MeasurableSpace SmallSeed]
    (ν : Measure SmallSeed) [IsProbabilityMeasure ν]
    (policy : Policy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)) SmallSeed) :
    freshPenalty input next old penalty ≤ freshObjective input next old policy.rule ν penalty :=
  iInf_le_of_le SmallSeed (iInf_le_of_le ‹MeasurableSpace SmallSeed›
    (iInf_le_of_le ν (iInf_le_of_le ‹IsProbabilityMeasure ν› (iInf_le_of_le policy le_rfl))))

theorem freshPenalty_le_penalty (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (penalty : ℝ≥0∞) : freshPenalty input next old penalty ≤ penalty := by
  let ν : Measure Unit := Measure.dirac ()
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have h := freshPenalty_le_policy input next old penalty ν
    (abandonPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)) Unit)
  rw [freshObjective, abandon_expectedObservationBill, zero_add] at h
  exact h.trans (by
    simpa only [mul_one] using
      (mul_le_mul_right (show freshRisk input next old
        (abandonPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
          (zeroNormalAccounting (I.freshSuffix next)) Unit).rule ν ≤ 1 from prob_le_one) penalty))

theorem freshRisk_encoded_eq (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (policy : Policy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)) Seed) (ν : Measure Seed) :
    freshRisk input next old (strategyPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next))
      .uncapped (zeroNormalAccounting (I.freshSuffix next))).rule
      (encodedSeedLaw (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
        (zeroNormalAccounting (I.freshSuffix next)) policy ν) = freshRisk input next old policy.rule ν := by
  unfold freshRisk
  have hm : Measurable (fun sample : Seed × (input.freshSuffix next).World =>
      (encodeSeed (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
        (zeroNormalAccounting (I.freshSuffix next)) policy sample.1, sample.2)) :=
    ((measurable_encodeSeed (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)) policy).comp measurable_fst).prodMk measurable_snd
  have hs : MeasurableSet {sample | ¬ freshSuccess input next old
      (strategyPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
        (zeroNormalAccounting (I.freshSuffix next))).rule sample} := by
    simpa only [Set.compl_ofPred] using (measurableSet_freshSuccess input next old
      (strategyPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
        (zeroNormalAccounting (I.freshSuffix next))).rule
      (strategyPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
        (zeroNormalAccounting (I.freshSuffix next))).measurable_rule).compl
  rw [seededWorldLaw_encoded (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
    (zeroNormalAccounting (I.freshSuffix next)) policy ν, Measure.map_apply hm hs]
  congr 1
  ext sample
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, freshSuccess, run_encoded_eq]

theorem freshPenalty_le_policy_any_seed (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (penalty : ℝ≥0∞) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : Policy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)) Seed) :
    freshPenalty input next old penalty ≤ freshObjective input next old policy.rule ν penalty := by
  have h := freshPenalty_le_policy input next old penalty
    (encodedSeedLaw (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)) policy ν)
    (strategyPolicy (input.freshSuffix next) (freshContract (I.freshSuffix next)) .uncapped
      (zeroNormalAccounting (I.freshSuffix next)))
  simpa only [freshObjective, expectedObservationBill_encoded_eq, freshRisk_encoded_eq] using h

theorem freshPenalty_ne_top (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    {penalty : ℝ≥0∞} (hfinite : penalty ≠ ⊤) : freshPenalty input next old penalty ≠ ⊤ :=
  ne_top_of_le_ne_top hfinite (freshPenalty_le_penalty input next old penalty)

/-- The toReal conversion is on a value already proved finite, never on
an arbitrary infinite policy bill or an infinite observation count. -/
noncomputable def freshPenaltyReal (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage) (penalty : ℝ) : ℝ :=
  (freshPenalty input next old (ENNReal.ofReal penalty)).toReal

end FreshPolicy

noncomputable def goodPenaltyReal {I : Instance} (input : StatisticalInput I) (stage : I.Stage) (old : Finset I.Stage) (penalty : ℝ) : ℝ :=
  freshPenaltyReal input (stage.val + 1) old penalty

noncomputable def badPenaltyReal {I : Instance} (input : StatisticalInput I) (stage : I.Stage) (old : Finset I.Stage) (penalty : ℝ) : ℝ :=
  if Matchable I (insert stage old) then freshPenaltyReal input (stage.val + 1) (insert stage old) penalty else penalty

def FreshPenaltyRecursion {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ (stage : I.Stage) (old : Finset I.Stage), Healthy I stage.val old → ∀ penalty : ℝ, 0 < penalty →
    freshPenaltyReal input stage.val old penalty = min penalty (goodPenaltyReal input stage old penalty +
      (input.experiment stage).localValueReal (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty))

def FreshPenaltyBoundaryClaims {I : Instance} (input : StatisticalInput I) : Prop :=
  (∀ next old penalty, ¬ Matchable I old → freshPenalty input next old penalty = penalty) ∧
  (∀ next old penalty, I.stageCount ≤ next → Matchable I old → freshPenalty input next old penalty = 0) ∧
  ∀ next old, Healthy I next old → errorRank I (stagesFrom I next) old = ⊤ →
    ∀ penalty, freshPenalty input next old penalty = 0

def FreshPenaltyAsymptotics {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ next old, Healthy I next old → ∀ depth : ℕ,
    errorRank I (stagesFrom I next) old = (depth : ℕ∞) →
      ∃ coefficient : ℝ, 0 < coefficient ∧ Asymptotics.IsEquivalent Filter.atTop
        (fun penalty : ℝ => freshPenaltyReal input next old penalty)
        (fun penalty : ℝ => coefficient * iteratedLog depth penalty)

def EqualRankCancellation {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ (stage : I.Stage) (old : Finset I.Stage), Healthy I stage.val old → Matchable I (insert stage old) →
    ∀ depth : ℕ, 1 ≤ depth →
      errorRank I (stagesFrom I (stage.val + 1)) old = (depth : ℕ∞) →
      errorRank I (stagesFrom I (stage.val + 1)) (insert stage old) = (depth : ℕ∞) →
      Asymptotics.IsLittleO Filter.atTop
        (fun penalty : ℝ => (input.experiment stage).localValueReal
          (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty))
        (fun penalty : ℝ => iteratedLog depth penalty)

/-- Analysis keeps observations, ordinary writes, and reports. Administrative
advances may be added by the uncapped rearrangement; the shadow history below
still contains the original complete visible history. -/
def informationEvent {I : Instance} : VisibleEvent I → Option (VisibleEvent I)
  | .observation i symbol => some (.observation i symbol)
  | .wrote i bit _ => some (.wrote i bit 0)
  | .report i truth _ => some (.report i truth 0)
  | _ => none

def informationTrace {I : Instance} (history : List (VisibleEvent I)) : List (VisibleEvent I) :=
  history.filterMap informationEvent

def TerminalOnly {I : Instance} (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) {Seed : Type u} (rule : PolicyRule I Seed) : Prop :=
  ∀ seed truth tapes n state, Prefix input C mode accounting rule seed truth tapes n state →
    state.cursor < I.stageCount → state.ledger.commitments = [] ∧ state.ledger.executions = []

noncomputable def eventualPairs {I : Instance} (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) {Seed : Type u} (rule : PolicyRule I Seed)
    (sample : Seed × input.World) : Finset (I.Stage × I.Tool) := by
  classical
  exact Finset.univ.filter (fun pair => ∃ n, ∃ execution ∈ (run input C mode accounting rule sample n).ledger.executions,
    execution.handle.stage = pair.1 ∧ execution.tool = pair.2)

/-- R02 analysis rearrangement. Its terminal payments use the old successful
run's actual PAIRS, not the upper script's arbitrary first matching.
All-path variable charges and all Seed universes are retained. The new
policy is uncapped; no claim of arbitrary-accounting native cap equality. -/
def NativeRearrangement {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I), C.IsEarlyRetained → ∀ (accounting : NormalAccounting I) (mode : ResourceMode)
    (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ policy : Policy input C mode accounting Seed,
      ∃ delayed : Policy input C .uncapped accounting Seed,
        TerminalOnly input C .uncapped accounting delayed.rule ∧
        ∃ shadow : Seed → List (VisibleEvent I) → List (VisibleEvent I),
          Measurable (fun pair : Seed × List (VisibleEvent I) => shadow pair.1 pair.2) ∧
          (∀ sample n, ∃ oldClock,
            shadow sample.1 (run input C .uncapped accounting delayed.rule sample n).history =
              (run input C mode accounting policy.rule sample oldClock).history ∧
            informationTrace (shadow sample.1 (run input C .uncapped accounting delayed.rule sample n).history) =
              informationTrace (run input C .uncapped accounting delayed.rule sample n).history) ∧
          (∀ sample, runSuccess input C mode accounting policy.rule sample →
            runSuccess input C .uncapped accounting delayed.rule sample ∧
            eventualPairs input C .uncapped accounting delayed.rule sample = eventualPairs input C mode accounting policy.rule sample ∧
            ∀ n, ∃ newClock, (informationTrace (run input C mode accounting policy.rule sample n).history).IsPrefix
              (informationTrace (run input C .uncapped accounting delayed.rule sample newClock).history)) ∧
          (∀ sample, runObservationBill input C .uncapped accounting delayed.rule sample ≤
            runObservationBill input C mode accounting policy.rule sample ∧
            runActualBill input C .uncapped accounting delayed.rule sample ≤ runActualBill input C mode accounting policy.rule sample) ∧
          ∀ (ν : Measure Seed), IsProbabilityMeasure ν →
            risk input C .uncapped accounting delayed.rule ν ≤ risk input C mode accounting policy.rule ν

def RankQueryCorrect (I : Instance) : Prop :=
  ∀ next old, (rankIndex I next old = none ↔ errorRank I (stagesFrom I next) old = ⊤) ∧
    ∀ depth, rankIndex I next old = some depth ↔ errorRank I (stagesFrom I next) old = (depth : ℕ∞)

def ReferenceAlignment {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I) (_hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (budget : ℚ),
    0 < budget → budget ≤ 1 / 2 → ∀ limit,
      TerminalOnly input C .uncapped accounting (retainedRule input budget limit) ∧
      ∀ sample n (stage : I.Stage),
        (run input C .uncapped accounting (retainedRule input budget limit) sample n).halted = false →
        (run input C .uncapped accounting (retainedRule input budget limit) sample n).cursor = stage.val →
        ∃ cache, replayBudget I budget (run input C .uncapped accounting (retainedRule input budget limit) sample n).history stage.val = some cache ∧
          Healthy I stage.val cache.errors ∧ ReferenceBudgetValid cache.risk ∧
          cache.errors = ordinaryMismatches (run input C .uncapped accounting (retainedRule input budget limit) sample n).ledger ∩ pastStages I stage.val

def TerminalScriptCompletion {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I), C.IsEarlyRetained → ∀ (accounting : NormalAccounting I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (sample : Unit × input.World) (n : ℕ),
    let state := run input C .uncapped accounting (retainedRule input budget limit) sample n
    state.halted = false → state.cursor = I.stageCount → allWritten state.ledger →
    Matchable I (ordinaryMismatches state.ledger) →
      ∃ later, n ≤ later ∧ (run input C .uncapped accounting (retainedRule input budget limit) sample later).halted = true ∧
        (run input C .uncapped accounting (retainedRule input budget limit) sample later).ledger.success C ∧
        (run input C .uncapped accounting (retainedRule input budget limit) sample later).ledger.executions.length =
          (ordinaryMismatches state.ledger).card

noncomputable def runFutureObservationBill {I : Instance} (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) {Seed : Type u} (rule : PolicyRule I Seed) (next : ℕ)
    (sample : Seed × input.World) : ℝ≥0∞ :=
  ⨆ n, ∑ i ∈ Finset.univ.filter (fun i : I.Stage => next ≤ i.val),
    ENNReal.ofReal (input.fees.observation i : ℝ) * ((run input C mode accounting rule sample n).ledger.reviews i : ℝ≥0∞)

/-- Full-history lower bridge without assuming a regular conditional
probability kernel. Gates see only the independent pre-birth view; all
observations already charged on ultimately failing paths are retained. -/
def FullHistoryPenaltyBridge {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ (stage : I.Stage) (old : Finset I.Stage), Healthy I stage.val old →
    ∀ (C : Contract I), C.IsEarlyRetained → ∀ (accounting : NormalAccounting I) (mode : ResourceMode)
      (Seed : Type u) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
        letI : IsProbabilityMeasure ν := hν
        ∀ (policy : Policy input C mode accounting Seed) (A : Set (Seed × input.PastWorld stage)), MeasurableSet A →
          (∀ sample, input.preBirthView stage sample ∈ A → ∃ history,
            entryHistory input C mode accounting policy.rule stage sample = some history ∧
              reportedErrors I history stage.val = old) →
          ∀ penalty : ℝ≥0∞,
            input.seededWorldLaw ν {sample | input.preBirthView stage sample ∈ A} * freshPenalty input stage.val old penalty ≤
              (∫⁻ sample, {sample | input.preBirthView stage sample ∈ A}.indicator
                (runFutureObservationBill input C mode accounting policy.rule stage.val) sample ∂input.seededWorldLaw ν) +
              penalty * input.seededWorldLaw ν {sample | input.preBirthView stage sample ∈ A ∧ ¬ runSuccess input C mode accounting policy.rule sample}

noncomputable def headCoefficient {I : Instance} (input : StatisticalInput I) : ℝ :=
  ∑ i ∈ girthHeads I, (input.experiment i).coefficient

theorem headCoefficient_pos {I : Instance} (input : StatisticalInput I) (hfinite : girth I ≠ ⊤) : 0 < headCoefficient input := by
  apply Finset.sum_pos
  · intro i _
    exact (input.experiment i).coefficient_pos
  · exact girthHeads_nonempty I hfinite

def NativeLowerPriceLaw {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ depth : ℕ, girth I = (depth : ℕ∞) → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ delta : ℝ, 0 < delta → delta < cutoff →
      ∀ (C : Contract I), C.IsEarlyRetained → ∀ accounting,
        ENNReal.ofReal ((1 - epsilon) * headCoefficient input * iteratedLog depth delta⁻¹) ≤
          value input C .native accounting (ENNReal.ofReal delta)

def ReferenceRiskAndCost {I : Instance} (input : StatisticalInput I) : Prop :=
  (∀ (C : Contract I) (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (budget : ℚ),
    0 < budget → budget ≤ 1 / 2 → risk input C .uncapped accounting
      (idealPolicy input C hretained accounting budget).rule (Measure.dirac ()) ≤ ENNReal.ofReal ((budget : ℝ) / 2)) ∧
  ∀ depth : ℕ, girth I = (depth : ℕ∞) → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
      ∀ (C : Contract I) (hretained : C.IsEarlyRetained) accounting,
        expectedBill input C .uncapped accounting (idealPolicy input C hretained accounting budget).rule (Measure.dirac ()) ≤
          ENNReal.ofReal ((1 + epsilon) * headCoefficient input * iteratedLog depth (budget : ℝ)⁻¹)

def TruncationAndNativeImplementation {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I) (hretained : C.IsEarlyRetained) accounting (delta : ℝ) (exponent : ℕ) (budget : ℚ),
    0 < delta → delta ≤ 1 / 2 → ReferenceRiskChoice I.stageCount delta exponent budget →
      (∀ sample, runActualBill input C .uncapped accounting
        (boundedPolicy input C hretained accounting budget exponent).rule sample ≤
          runActualBill input C .uncapped accounting (idealPolicy input C hretained accounting budget).rule sample) ∧
      risk input C .uncapped accounting (boundedPolicy input C hretained accounting budget exponent).rule (Measure.dirac ()) ≤
        risk input C .uncapped accounting (idealPolicy input C hretained accounting budget).rule (Measure.dirac ()) + ENNReal.ofReal (delta / 2) ∧
      (∀ sample n, (∀ i, (run input C .uncapped accounting (boundedPolicy input C hretained accounting budget exponent).rule sample n).ledger.reviews i ≤ referenceQuota input exponent i) ∧
        (run input C .uncapped accounting (boundedPolicy input C hretained accounting budget exponent).rule sample n).ledger.executions.length ≤ min I.stageCount I.toolCount) ∧
      (OriginalQualification input C hretained accounting budget exponent →
        ∃ policy : Policy input C .native accounting Unit,
          policy.rule = (boundedPolicy input C hretained accounting budget exponent).rule ∧
          ∀ sample n, run input C .native accounting policy.rule sample n =
            run input C .uncapped accounting (boundedPolicy input C hretained accounting budget exponent).rule sample n)

def NativeUpperPriceLaw {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ depth : ℕ, girth I = (depth : ℕ∞) → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ (delta : ℝ) (exponent : ℕ) (budget : ℚ),
      0 < delta → delta < cutoff → delta ≤ 1 / 2 → ReferenceRiskChoice I.stageCount delta exponent budget →
        ∀ (C : Contract I) (hretained : C.IsEarlyRetained) accounting,
          OriginalQualification input C hretained accounting budget exponent →
            ∃ policy : Policy input C .native accounting Unit,
              policy.rule = (boundedPolicy input C hretained accounting budget exponent).rule ∧
              risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
              expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
                ENNReal.ofReal ((1 + epsilon) * headCoefficient input * iteratedLog depth delta⁻¹) ∧
              value input C .native accounting (ENNReal.ofReal delta) ≤ expectedBill input C .native accounting policy.rule (Measure.dirac ())

def NativeInfiniteGirthLaw {I : Instance} (input : StatisticalInput I) : Prop :=
  girth I = ⊤ → ∀ (C : Contract I) (hretained : C.IsEarlyRetained) accounting (budget : ℚ) (exponent : ℕ),
    0 < budget → budget ≤ 1 / 2 → OriginalQualification input C hretained accounting budget exponent →
      ∃ policy : Policy input C .native accounting Unit,
        policy.rule = (boundedPolicy input C hretained accounting budget exponent).rule ∧
        risk input C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
        expectedObservationBill input C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
        expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
          (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection

def RetainedPriceClaims {I : Instance} (input : StatisticalInput I) : Prop :=
  NativeRearrangement.{u} input ∧ FullHistoryPenaltyBridge.{u} input ∧ FreshPenaltyRecursion input ∧
    FreshPenaltyBoundaryClaims input ∧ FreshPenaltyAsymptotics input ∧ EqualRankCancellation input ∧
    ReferenceAlignment input ∧ TerminalScriptCompletion input ∧ ReferenceRiskAndCost input ∧
    TruncationAndNativeImplementation input ∧ NativeLowerPriceLaw input ∧ NativeUpperPriceLaw input ∧ NativeInfiniteGirthLaw input

end PaperProofs.Retained
