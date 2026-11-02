module

public import PaperProofs.Retained.PRet_Alignment_Actual_005
public import PaperProofs.Retained.PRet_NativeImplementation_118
public import PaperProofs.Common.ReferenceTermination
public import PaperProofs.Common.NativeCostBound

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace RootRetainedInfinite

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained

variable {I : Instance}

theorem rankIndex_none (top : girth I = ⊤) (next : ℕ) (old : Finset I.Stage) :
    rankIndex I next old = none := by
  classical
  have full := (girth_eq_top_iff_matchable_univ I).mp top
  unfold rankIndex
  apply List.find?_eq_none.mpr
  intro depth _ hunsafe
  simp only [unsafeBudget, decide_eq_true_eq] at hunsafe
  obtain ⟨future, _, _, bad⟩ := hunsafe
  exact bad (full.subset (Finset.subset_univ _))

theorem rankCase_infinite (top : girth I = ⊤) (stage : I.Stage) (old : Finset I.Stage) :
    rankCase I stage old = some .infiniteRank := by
  simp only [rankCase, rankIndex_none top]

theorem testing_eq_write (input : StatisticalInput I) (top : girth I = ⊤)
    (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I))
    (cache : BudgetCache I) (stage : I.Stage) :
    retainedTestingAction input limit history cache stage = .write stage false := by
  simp only [retainedTestingAction, rankCase_infinite top]

theorem candidate_limit_eq (input : StatisticalInput I) (top : girth I = ⊤)
    (budget : ℚ) (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I)) :
    retainedCandidate input budget limit history = retainedCandidate input budget none history := by
  simp only [retainedCandidate, testing_eq_write input top]

theorem rule_limit_eq (input : StatisticalInput I) (top : girth I = ⊤)
    (budget : ℚ) (limit : ReferenceObservationLimit I) :
    retainedRule input budget limit = retainedRule input budget none := by
  funext seed history
  simp only [retainedRule, PRetRetainedGuard007.guarded, candidate_limit_eq input top]

theorem terminal_ne_review (history : List (VisibleEvent I)) (stage : I.Stage) :
    terminalMatchingAction I history ≠ .review stage := by
  unfold terminalMatchingAction
  dsimp only
  repeat' first | split | (intro impossible; cases impossible)

theorem candidate_ne_review (input : StatisticalInput I) (top : girth I = ⊤)
    (budget : ℚ) (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I)) (stage : I.Stage) :
    retainedCandidate input budget limit history ≠ .review stage := by
  unfold retainedCandidate
  split
  · simp
  · split
    · dsimp only
      split
      · simp
      · split
        · simp
        · split
          · rw [testing_eq_write input top]
            intro impossible
            cases impossible
          · split
            · simp
            · split_ifs <;> simp
    · split
      · exact terminal_ne_review history stage
      · simp

theorem rule_ne_review (input : StatisticalInput I) (top : girth I = ⊤)
    (budget : ℚ) (limit : ReferenceObservationLimit I) (seed : Unit)
    (history : List (VisibleEvent I)) (stage : I.Stage) :
    retainedRule input budget limit seed history ≠ .review stage := by
  unfold retainedRule PRetRetainedGuard007.guarded
  split
  · exact candidate_ne_review input top budget limit history stage
  · simp

end RootRetainedInfinite
