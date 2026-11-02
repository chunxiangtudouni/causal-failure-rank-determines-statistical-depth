module

public import PaperProofs.Retained.PRet_Completion_Original_006
public import PaperProofs.Common.ReferenceDecisionRealization

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetRiskMassFlow

variable {I : Instance}

def cacheTarget (I : Instance) (stage : I.Stage) (cache : BudgetCache I) : Option ℚ :=
  if 0 < cache.risk ∧ cache.risk ≤ 1/4 then
    (rankCase I stage cache.errors).bind (fun kind => referenceBudgetTarget kind cache.risk)
  else none

def entryTarget (I : Instance) (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) : Option ℚ :=
  (replayBudget I budget history stage.val).bind (cacheTarget I stage)

theorem cacheTarget_eq (stage : I.Stage) (cache : BudgetCache I) (valid : ReferenceBudgetValid cache.risk) :
    cacheTarget I stage cache = (rankCase I stage cache.errors).bind (fun kind => referenceBudgetTarget kind cache.risk) := by
  unfold cacheTarget
  exact ite_eq_left valid

theorem entryTarget_eq (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) (cache : BudgetCache I)
    (replay : replayBudget I budget history stage.val = some cache) :
    entryTarget I budget stage history = cacheTarget I stage cache := by
  unfold entryTarget
  rw [replay]
  rfl

theorem entryTarget_congr (budget : ℚ) (stage : I.Stage) (left right : List (VisibleEvent I))
    (replay : replayBudget I budget left stage.val = replayBudget I budget right stage.val) :
    entryTarget I budget stage left = entryTarget I budget stage right := by
  unfold entryTarget
  rw [replay]

theorem cacheTarget_valid (stage : I.Stage) (cache : BudgetCache I) (p : ℚ)
    (target : cacheTarget I stage cache = some p) : 0 < p ∧ p ≤ 1/4 := by
  unfold cacheTarget at target
  by_cases valid : 0 < cache.risk ∧ cache.risk ≤ 1/4
  · rw [ite_eq_left valid] at target
    obtain ⟨kind,_query,chosen⟩ := Option.bind_eq_some_iff.mp target
    have bound := referenceBudgetTarget_valid_floor kind cache.risk p valid chosen
    exact ⟨bound.1,bound.2.1⟩
  · rw [ite_eq_right valid] at target
    cases target

theorem entryTarget_valid (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) (p : ℚ)
    (target : entryTarget I budget stage history = some p) : 0 < p ∧ p ≤ 1/4 := by
  obtain ⟨cache,_replay,chosen⟩ := Option.bind_eq_some_iff.mp target
  exact cacheTarget_valid stage cache p chosen

theorem candidate_at_open (input : StatisticalInput I) (budget : ℚ) (history : List (VisibleEvent I))
    (stage : I.Stage) (cache : BudgetCache I) (active : historyHalted history = false)
    (cursor : historyCursor history = stage.val) (replay : replayBudget I budget history stage.val = some cache)
    (healthy : Healthy I stage.val cache.errors) (valid : ReferenceBudgetValid cache.risk)
    (openPort : historyWrite history stage = none) :
    retainedCandidate input budget none history = retainedTestingAction input none history cache stage := by
  have before : historyCursor history < I.stageCount := cursor ▸ stage.isLt
  have stageEq : (⟨historyCursor history,before⟩ : I.Stage) = stage := Fin.ext cursor
  unfold retainedCandidate
  simp only [active,Bool.false_eq_true,↓reduceIte,dite_eq_left before,stageEq]
  rw [cursor,replay]
  dsimp only
  have good : ¬(¬Healthy I stage.val cache.errors ∨ ¬(0<cache.risk ∧ cache.risk≤1/4)) :=
    not_or.mpr ⟨not_not.mpr healthy,not_not.mpr valid⟩
  rw [ite_eq_right good,openPort]

end PRetRiskMassFlow
