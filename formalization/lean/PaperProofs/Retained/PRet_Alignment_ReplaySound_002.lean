module

public import PaperProofs.Retained.PRet_Alignment_RankCase_001
public import PaperProofs.Retained.PRet_BudgetReplay_117

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics

namespace PRetAlignment

variable {I : Instance}

theorem reportedErrors_zero (history : List (VisibleEvent I)) : reportedErrors I history 0 = ∅ := by
  ext stage
  simp [reportedErrors]

theorem reportedErrors_succ (history : List (VisibleEvent I)) (stage : I.Stage) (error : Bool)
    (reported : reportedError history stage = some error) :
    reportedErrors I history (stage.val+1) =
      if error then insert stage (reportedErrors I history stage.val) else reportedErrors I history stage.val := by
  classical
  ext j
  by_cases eq : j = stage
  · subst j
    cases error <;> simp [reportedErrors, reported]
  · have ne : j.val ≠ stage.val := fun h => eq (Fin.ext h)
    have lt : j.val < stage.val + 1 ↔ j.val < stage.val := by omega
    cases error <;> simp only [Bool.false_eq_true, ↓reduceIte,
      reportedErrors, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, eq, false_or] <;>
      exact and_congr_left (fun _ => lt)

theorem replayStep_sound (history : List (VisibleEvent I)) (cache next : BudgetCache I) (stage : I.Stage)
    (healthy : Healthy I stage.val cache.errors) (valid : ReferenceBudgetValid cache.risk)
    (errors : cache.errors = reportedErrors I history stage.val)
    (step : replayBudgetStep I history cache stage = some next) :
    Healthy I (stage.val+1) next.errors ∧ ReferenceBudgetValid next.risk ∧
      next.errors = reportedErrors I history (stage.val+1) := by
  classical
  unfold replayBudgetStep at step
  cases report : reportedError history stage with
  | none => rw [report] at step; cases step
  | some error =>
    rw [report] at step
    dsimp at step
    cases query : rankCase I stage cache.errors with
    | none => rw [query] at step; cases step
    | some kind =>
      rw [query] at step
      dsimp at step
      cases child : referenceBudgetStep kind error cache.risk with
      | none => rw [child] at step; cases step
      | some risk =>
        rw [child] at step
        change (if Matchable I (if error then insert stage cache.errors else cache.errors) then
          some (⟨if error then insert stage cache.errors else cache.errors,risk⟩ : BudgetCache I) else none) = some next at step
        by_cases matchable : Matchable I (if error then insert stage cache.errors else cache.errors)
        · rw [ite_eq_left matchable] at step
          have eq := Option.some.inj step
          subst next
          refine ⟨?_, (referenceBudgetStep_valid_floor kind error cache.risk risk valid child).1, ?_⟩
          · cases error with
            | false => exact healthy_correct I stage cache.errors healthy
            | true => exact (healthy_error_iff I stage cache.errors healthy).mpr matchable
          · dsimp
            rw [reportedErrors_succ history stage error report, errors]
        · rw [ite_eq_right matchable] at step
          cases step

theorem replayBudget_sound (budget : ℚ) (history : List (VisibleEvent I)) (hbudget : ReferenceBudgetValid (budget/2))
    (next : ℕ) (bound : next ≤ I.stageCount) (cache : BudgetCache I)
    (replay : replayBudget I budget history next = some cache) :
    Healthy I next cache.errors ∧ ReferenceBudgetValid cache.risk ∧
      cache.errors = reportedErrors I history next := by
  induction next generalizing cache with
  | zero =>
    have eq : (⟨∅,budget/2⟩ : BudgetCache I) = cache := Option.some.inj replay
    subst cache
    exact ⟨healthy_initial I, hbudget, (reportedErrors_zero history).symm⟩
  | succ n ih =>
    let stage : I.Stage := ⟨n, by change n < I.stageCount; omega⟩
    change replayBudget I budget history (stage.val+1) = some cache at replay
    rw [PRetBudgetReplay117.replayBudget_succ] at replay
    cases old : replayBudget I budget history stage.val with
    | none => rw [old] at replay; cases replay
    | some previous =>
      rw [old] at replay
      dsimp at replay
      obtain ⟨healthy,valid,errors⟩ := ih (by omega) previous old
      exact replayStep_sound history previous cache stage healthy valid errors replay

end PRetAlignment
