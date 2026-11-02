module

public import PaperProofs.Star.RootStarOverflow_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

theorem testingAction_quota_exhausted (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) :
    P.testingActionReal order kind r (some quota) history stage = P.testingActionReal order kind r none history stage ∨
      P.testingActionReal order kind r none history stage = .review stage ∧
        quota ≤ (historyObservations history stage).length ∧
        P.testingActionReal order kind r (some quota) history stage = .abandon := by
  classical
  cases ht : P.chosenTargetReal order kind r history stage with
  | none => exact Or.inl (by simp only [testingActionReal, ht])
  | some target =>
    by_cases hv : ∀ symbol ∈ historyObservations history stage, symbol < P.channel.experiment.alphabetSize
    · simp only [testingActionReal, ht, dite_eq_left hv]
      split
      · exact Or.inl rfl
      · by_cases hq : (historyObservations history stage).length < quota
        · exact Or.inl (by simp only [ite_eq_left hq])
        · exact Or.inr ⟨rfl, Nat.le_of_not_lt hq, by simp only [ite_eq_right hq]⟩
    · exact Or.inl (by simp only [testingActionReal, ht, dite_eq_right hv])

theorem starRule_quota_exhausted {Seed : Type*} (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (seed : Seed) (history : List (VisibleEvent (starInstance P.tools order))) :
    P.starReferenceRule order kind r (some quota) seed history = P.starReferenceRule order kind r none seed history ∨
      ∃ stage, P.starReferenceRule order kind r none seed history = .review stage ∧
        quota ≤ (historyObservations history stage).length ∧
        P.starReferenceRule order kind r (some quota) seed history = .abandon := by
  by_cases hh : historyHalted history = true
  · exact Or.inl (by simp only [starReferenceRule, candidateWithTesting, hh, ↓reduceIte])
  · by_cases hs : historyCursor history < (starInstance P.tools order).stageCount
    · cases hw : historyWritten history ⟨historyCursor history, hs⟩ with
      | none =>
        rcases testingAction_quota_exhausted P order kind r quota history ⟨historyCursor history, hs⟩ with heq | ⟨hi, hq, hb⟩
        · exact Or.inl (by simpa only [starReferenceRule, candidateWithTesting, ite_eq_right hh, dite_eq_left hs, hw] using heq)
        · refine Or.inr ⟨⟨historyCursor history, hs⟩, ?_, hq, ?_⟩
          · simpa only [starReferenceRule, candidateWithTesting, ite_eq_right hh, dite_eq_left hs, hw] using hi
          · simpa only [starReferenceRule, candidateWithTesting, ite_eq_right hh, dite_eq_left hs, hw] using hb
      | some bit => exact Or.inl (by simp only [starReferenceRule, candidateWithTesting, ite_eq_right hh, dite_eq_left hs, hw])
    · exact Or.inl (by simp only [starReferenceRule, candidateWithTesting, ite_eq_right hh, dite_eq_right hs])

end RootStarOverflow
