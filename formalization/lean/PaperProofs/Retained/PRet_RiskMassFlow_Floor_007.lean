module

public import PaperProofs.Retained.PRet_RiskMassFlow_Target_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory

namespace PRetRiskMassFlow

variable {I : Instance}

theorem replayStep_risk_floor (history : List (VisibleEvent I)) (cache next : BudgetCache I) (stage : I.Stage)
    (valid : ReferenceBudgetValid cache.risk) (step : replayBudgetStep I history cache stage = some next) :
    ReferenceBudgetValid next.risk ∧ cache.risk/2 ≤ next.risk := by
  classical
  unfold replayBudgetStep at step
  obtain ⟨error,_report,rest⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨kind,_query,rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨risk,update,rest⟩ := Option.bind_eq_some_iff.mp rest
  by_cases matchable : Matchable I (if error then insert stage cache.errors else cache.errors)
  · rw [ite_eq_left matchable] at rest
    have cacheEq := Option.some.inj rest
    have riskEq : risk = next.risk := congrArg BudgetCache.risk cacheEq
    rw [← riskEq]
    exact referenceBudgetStep_valid_floor kind error cache.risk risk valid update
  · rw [ite_eq_right matchable] at rest
    cases rest

theorem replayBudget_risk_floor (budget : ℚ) (history : List (VisibleEvent I))
    (initialValid : ReferenceBudgetValid (budget/2)) (next : ℕ) (bound : next ≤ I.stageCount)
    (cache : BudgetCache I) (replay : replayBudget I budget history next = some cache) :
    ReferenceBudgetValid cache.risk ∧ budget/(2:ℚ)^(next+1) ≤ cache.risk := by
  induction next generalizing cache with
  | zero =>
    have eq : (⟨∅,budget/2⟩ : BudgetCache I) = cache := Option.some.inj replay
    subst cache
    exact ⟨initialValid,by simp only [Nat.zero_add,pow_one,le_refl]⟩
  | succ n ih =>
    let stage : I.Stage := ⟨n,by change n < I.stageCount; omega⟩
    change replayBudget I budget history (stage.val+1) = some cache at replay
    rw [PRetBudgetReplay117.replayBudget_succ] at replay
    cases old : replayBudget I budget history stage.val with
    | none => rw [old] at replay; cases replay
    | some previous =>
      rw [old] at replay
      obtain ⟨valid,lower⟩ := ih (by omega) previous old
      obtain ⟨childValid,childLower⟩ := replayStep_risk_floor history previous cache stage valid replay
      refine ⟨childValid,?_⟩
      calc
        budget/(2:ℚ)^(n+1+1) = (budget/(2:ℚ)^(n+1))/2 := by rw [pow_succ,div_mul_eq_div_div]
        _ ≤ previous.risk/2 := div_le_div_of_nonneg_right lower (by norm_num)
        _ ≤ cache.risk := childLower

theorem cacheTarget_floor (stage : I.Stage) (cache : BudgetCache I) (p : ℚ)
    (valid : ReferenceBudgetValid cache.risk) (target : cacheTarget I stage cache = some p) : cache.risk/6 ≤ p := by
  rw [cacheTarget_eq stage cache valid] at target
  obtain ⟨kind,_query,chosen⟩ := Option.bind_eq_some_iff.mp target
  exact (referenceBudgetTarget_valid_floor kind cache.risk p valid chosen).2.2

theorem entryTarget_floor (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (p : ℚ)
    (target : entryTarget I budget stage history = some p) : budget/(2:ℚ)^(stage.val+1)/6 ≤ p := by
  obtain ⟨cache,replay,chosen⟩ := Option.bind_eq_some_iff.mp target
  have initialValid : ReferenceBudgetValid (budget/2) := by constructor <;> linarith
  obtain ⟨valid,lower⟩ := replayBudget_risk_floor budget history initialValid stage.val (Nat.le_of_lt stage.isLt) cache replay
  exact (div_le_div_of_nonneg_right lower (by norm_num)).trans (cacheTarget_floor stage cache p valid chosen)

end PRetRiskMassFlow
