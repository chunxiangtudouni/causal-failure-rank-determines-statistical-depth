module

public import PaperProofs.Retained.PDROC_RetainedEnvelope_001
public import PaperProofs.Retained.PRet_RiskMassFlow_Rank_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Retained PaperProofs.Statistics
open PaperProofs.Retained.PRetObservationEnvelope119

namespace PDROC.RetainedEnvelopeRun.Branch

variable {I : Instance}

/-- Exactly the original good child, except that infinite retained rank
has zero future observation allowance. -/
noncomputable def goodAllowance (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (kind : ReferenceBudgetCase) (risk : ℚ) : ℝ≥0∞ :=
  match kind with
  | .infiniteRank => 0
  | .noTool | .finiteBad _ => observationEnvelope input (stage.val + 1) old (risk / 2)

/-- Only the finite-bad branch has a potentially observed bad child. The
target and rational bad-risk clamp are precisely those of the original script. -/
noncomputable def badAllowance (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (kind : ReferenceBudgetCase) (risk : ℚ) : ℝ≥0∞ :=
  match kind with
  | .finiteBad depth => observationEnvelope input (stage.val + 1) (insert stage old)
      (controllerBadRisk risk (controllerTarget risk depth.val))
  | .infiniteRank | .noTool => 0

theorem currentEnvelope_decomposition (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (kind : ReferenceBudgetCase) (risk : ℚ)
    (query : rankCase I stage old = some kind) :
    observationEnvelope input stage.val old risk =
      localObservationPrice input stage kind risk + goodAllowance input stage old kind risk +
        (match referenceBudgetTarget kind risk with
          | none => 0
          | some p => ENNReal.ofReal (p : ℝ)) * badAllowance input stage old kind risk := by
  rw [observationEnvelope_step, query]
  cases kind with
  | infiniteRank => simp [goodAllowance, badAllowance, localObservationPrice, referenceBudgetTarget]
  | noTool => simp [goodAllowance, badAllowance]
  | finiteBad depth => rfl

/-- Reuse the original numerical zero-envelope argument with the existing
flat rank query proof. No conflicting formal-query import is introduced. -/
theorem envelope_zero_of_rank_top (input : StatisticalInput I) (next : ℕ)
    (old : Finset I.Stage) (risk : ℚ)
    (ht : errorRank I (stagesFrom I next) old = ⊤) :
    observationEnvelope input next old risk = 0 := by
  by_cases hn : next < I.stageCount
  · let stage : I.Stage := ⟨next, hn⟩
    have hq : rankIndex I next old = none := (RootRetainedQueries.rankQueryCorrect I next old).1.mpr ht
    have hc : rankCase I stage old = some .infiniteRank := by
      simp only [rankCase, stage, hq]
    change observationEnvelope input stage.val old risk = 0
    rw [observationEnvelope_step, hc]
  · exact observationEnvelope_past_end input next old risk (Nat.le_of_not_gt hn)

theorem rankCase_infiniteRank_iff_top (stage : I.Stage) (old : Finset I.Stage) :
    rankCase I stage old = some .infiniteRank ↔ errorRank I (stagesFrom I stage.val) old = ⊤ := by
  constructor
  · intro query
    have hindex : rankIndex I stage.val old = none := by
      cases hi : rankIndex I stage.val old with
      | none => rfl
      | some depth =>
        simp only [rankCase, hi] at query
        split at query
        · cases query
        · split at query
          · cases query
          · split at query <;> cases query
    exact (RootRetainedQueries.rankQueryCorrect I stage.val old).1.mp hindex
  · intro ht
    have hindex := (RootRetainedQueries.rankQueryCorrect I stage.val old).1.mpr ht
    simp only [rankCase, hindex]

theorem infinite_rank_children (stage : I.Stage) (old : Finset I.Stage)
    (healthy : Healthy I stage.val old) (ht : errorRank I (stagesFrom I stage.val) old = ⊤) :
    errorRank I (stagesFrom I (stage.val + 1)) old = ⊤ ∧
      errorRank I (stagesFrom I (stage.val + 1)) (insert stage old) = ⊤ := by
  have hs := RootRetainedAsymp.rank_suffix_step stage old healthy
  rw [ht] at hs
  have hg : errorRank I (stagesFrom I (stage.val + 1)) old = ⊤ := by
    apply top_le_iff.mp
    rw [hs]
    exact min_le_left _ _
  have hb : 1 + errorRank I (stagesFrom I (stage.val + 1)) (insert stage old) = ⊤ := by
    apply top_le_iff.mp
    rw [hs]
    exact min_le_right _ _
  exact ⟨hg, (ENat.add_eq_top.mp hb).resolve_left (by simp)⟩

/-- The original cache transition is dominated by exactly the original
numerical branch allowance. This is pure cache algebra, with no run premise. -/
theorem childEnvelope_le_allowance (input : StatisticalInput I) (stage : I.Stage)
    (cache child : BudgetCache I) (kind : ReferenceBudgetCase) (error : Bool)
    (healthy : Healthy I stage.val cache.errors)
    (query : rankCase I stage cache.errors = some kind)
    (step : referenceBudgetStep kind error cache.risk = some child.risk)
    (errors : child.errors = if error then insert stage cache.errors else cache.errors) :
    observationEnvelope input (stage.val + 1) child.errors child.risk ≤
      if error then badAllowance input stage cache.errors kind cache.risk
      else goodAllowance input stage cache.errors kind cache.risk := by
  cases kind with
  | infiniteRank =>
    have ht := (rankCase_infiniteRank_iff_top stage cache.errors).mp query
    have children := infinite_rank_children stage cache.errors healthy ht
    have hc : errorRank I (stagesFrom I (stage.val + 1)) child.errors = ⊤ := by
      rw [errors]
      cases error with
      | false => exact children.1
      | true => exact children.2
    rw [envelope_zero_of_rank_top input (stage.val + 1) child.errors child.risk hc]
    exact bot_le
  | noTool =>
    cases error with
    | false =>
      have hr : cache.risk / 2 = child.risk := Option.some.inj step
      simp only [errors, ← hr, goodAllowance, Bool.false_eq_true, ite_false, le_refl]
    | true => cases step
  | finiteBad depth =>
    cases error with
    | false =>
      have hr : cache.risk / 2 = child.risk := Option.some.inj step
      simp only [errors, ← hr, goodAllowance, Bool.false_eq_true, ite_false, le_refl]
    | true =>
      have hr : controllerBadRisk cache.risk (controllerTarget cache.risk depth.val) = child.risk :=
        Option.some.inj step
      simp only [errors, ← hr, badAllowance, ite_true, le_refl]

end PDROC.RetainedEnvelopeRun.Branch
