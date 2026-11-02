module

public import PaperProofs.Retained.Controller
public import PaperProofs.Common.ReferenceTruncation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetTruncation120

open Common Common.Native Statistics MeasureTheory
open scoped ENNReal

variable {I : Instance}

/-- A real pending review in the original ideal retained interpreter,
including failed paths, at or beyond the chosen original stage quota. -/
def retainedOverflow (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (quota : I.Stage → ℕ) : Set (Unit × input.World) :=
  {sample | ∃ (n : ℕ) (stage : I.Stage),
    let state := run input C .uncapped accounting
      (idealPolicy input C hretained accounting budget).rule sample n
    state.halted = false ∧
    (idealPolicy input C hretained accounting budget).rule () state.history = .review stage ∧
      (quota stage : ℕ∞) ≤ state.ledger.reviews stage}

theorem retainedTestingAction_quota_coupling (input : StatisticalInput I)
    (quota : I.Stage → ℕ) (history : List (VisibleEvent I))
    (cache : BudgetCache I) (stage : I.Stage) :
    retainedTestingAction input (some quota) history cache stage =
      retainedTestingAction input none history cache stage ∨
    (retainedTestingAction input none history cache stage = .review stage ∧
      quota stage ≤ (historyObservations history stage).length ∧
      retainedTestingAction input (some quota) history cache stage = .abandon) := by
  cases hk : rankCase I stage cache.errors with
  | none => exact Or.inl (by simp only [retainedTestingAction, hk])
  | some kind =>
    cases kind with
    | infiniteRank => exact Or.inl (by simp only [retainedTestingAction, hk])
    | noTool | finiteBad depth =>
      cases ht : (rankCase I stage cache.errors).bind (fun kind => referenceBudgetTarget kind cache.risk) with
      | none =>
        apply Or.inl
        simp only [retainedTestingAction, ht]
      | some target =>
        simp only [retainedTestingAction, ht]
        rw [hk]
        dsimp only
        by_cases hv : ∀ symbol ∈ historyObservations history stage,
            symbol < (input.experiment stage).alphabetSize
        · simp only [dite_eq_left hv]
          by_cases hit : (input.experiment stage).rationalWordHits target
              (historyObservationWord input history stage hv) = true
          · exact Or.inl (by simp only [hit, ↓reduceIte])
          · simp only [ite_eq_right hit]
            by_cases below : (historyObservations history stage).length < quota stage
            · exact Or.inl (by simp only [ite_eq_left below])
            · exact Or.inr ⟨trivial, Nat.le_of_not_lt below, by simp only [ite_eq_right below]⟩
        · exact Or.inl (by simp only [dite_eq_right hv])

theorem retainedCandidate_quota_coupling (input : StatisticalInput I) (budget : ℚ)
    (quota : I.Stage → ℕ) (history : List (VisibleEvent I)) :
    retainedCandidate input budget (some quota) history = retainedCandidate input budget none history ∨
    ∃ stage : I.Stage, retainedCandidate input budget none history = .review stage ∧
      quota stage ≤ (historyObservations history stage).length ∧
      retainedCandidate input budget (some quota) history = .abandon := by
  classical
  unfold retainedCandidate
  split
  · exact Or.inl rfl
  · split
    · dsimp only
      split
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · split
          · rcases retainedTestingAction_quota_coupling input quota history _ _ with same | different
            · exact Or.inl same
            · exact Or.inr ⟨_, different⟩
          · exact Or.inl rfl
    · exact Or.inl rfl

theorem retainedRule_quota_coupling (input : StatisticalInput I) (budget : ℚ) (quota : I.Stage → ℕ)
    (seed : Unit) (history : List (VisibleEvent I)) :
    retainedRule input budget (some quota) seed history = retainedRule input budget none seed history ∨
    ∃ stage : I.Stage, retainedRule input budget none seed history = .review stage ∧
      quota stage ≤ (historyObservations history stage).length ∧
      retainedRule input budget (some quota) seed history = .abandon := by
  rcases retainedCandidate_quota_coupling input budget quota history with same | ⟨stage, ideal, reached, bounded⟩
  · exact Or.inl (by simp only [retainedRule, PRetRetainedGuard007.guarded, same])
  · have boundedGuard : retainedRule input budget (some quota) seed history = .abandon := by
      change (if PRetRetainedGuard007.allows history (retainedCandidate input budget (some quota) history)
        then retainedCandidate input budget (some quota) history else .abandon) = .abandon
      rw [bounded]
      exact ite_self _
    by_cases permitted : PRetRetainedGuard007.allows history (retainedCandidate input budget none history)
    · refine Or.inr ⟨stage, ?_, reached, ?_⟩
      · simpa only [retainedRule, PRetRetainedGuard007.guarded, ite_eq_left permitted] using ideal
      · exact boundedGuard
    · apply Or.inl
      exact boundedGuard.trans (ite_eq_right permitted).symm

theorem retainedRun_quota_coupling (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (quota : I.Stage → ℕ)
    (sample : Unit × input.World) (n : ℕ) :
    let ideal := retainedRule input budget none
    let bounded := retainedRule input budget (some quota)
    run input C .uncapped accounting bounded sample n = run input C .uncapped accounting ideal sample n ∨
      (sample ∈ retainedOverflow input C hretained accounting budget quota ∧
        ∃ k < n, run input C .uncapped accounting bounded sample n =
          stopState (run input C .uncapped accounting ideal sample k) true) := by
  let ideal := retainedRule input budget none
  let bounded := retainedRule input budget (some quota)
  change run input C .uncapped accounting bounded sample n = run input C .uncapped accounting ideal sample n ∨ _
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rcases ih with heq | ⟨hoverflow, k, hkn, haborted⟩
    · by_cases hh : (run input C .uncapped accounting ideal sample n).halted = true
      · have hhb : (run input C .uncapped accounting bounded sample n).halted = true := by rw [heq]; exact hh
        exact Or.inl (by rw [run_succ_of_halted input C .uncapped accounting bounded sample n hhb,
          run_succ_of_halted input C .uncapped accounting ideal sample n hh, heq])
      · have hactive : (run input C .uncapped accounting ideal sample n).halted = false :=
          Bool.eq_false_iff.mpr hh
        rcases retainedRule_quota_coupling input budget quota sample.1
            (run input C .uncapped accounting ideal sample n).history with hsame | ⟨stage, hi, hq, hb⟩
        · exact Or.inl (by
            simp only [run]
            rw [heq]
            change nextFromFrontier input C .uncapped accounting _
              (retainedRule input budget (some quota) sample.1 _) _ = _
            rw [hsame])
        · have hidealLegal : LegalRule input C .uncapped accounting ideal :=
            retainedRule_uncapped_legal input C hretained accounting budget none
          obtain ⟨prefixLength, _, hp⟩ := run_has_prefix input C .uncapped accounting ideal hidealLegal sample n
          have hqledger : (quota stage : ℕ∞) ≤ (run input C .uncapped accounting ideal sample n).ledger.reviews stage := by
            rw [← prefix_historyObservations_length input C .uncapped accounting ideal sample.1
              (input.truthAt sample.2) (worldTapes input sample.2) hp stage]
            exact_mod_cast hq
          have ho : sample ∈ retainedOverflow input C hretained accounting budget quota :=
            ⟨n, stage, hactive, hi, hqledger⟩
          have hactiveb : (run input C .uncapped accounting bounded sample n).halted = false := by rw [heq]; exact hactive
          have hstep : Step input C .uncapped accounting (worldTapes input sample.2)
              (run input C .uncapped accounting bounded sample n)
              (bounded sample.1 (run input C .uncapped accounting bounded sample n).history)
              (stopState (run input C .uncapped accounting ideal sample n) true) := by
            rw [heq]
            change Step input C .uncapped accounting _ _
              (retainedRule input budget (some quota) sample.1 _) _
            rw [hb]
            exact .abandon _ hactive
          exact Or.inr ⟨ho, n, Nat.lt_succ_self n,
            run_succ_of_step input C .uncapped accounting bounded sample n _ hactiveb hstep⟩
    · have hhb : (run input C .uncapped accounting bounded sample n).halted = true := by
        rw [haborted]
        rfl
      exact Or.inr ⟨hoverflow, k, hkn.trans (Nat.lt_succ_self n), by
        rw [run_succ_of_halted input C .uncapped accounting bounded sample n hhb]
        exact haborted⟩

theorem retainedRun_eq_of_not_overflow (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (quota : I.Stage → ℕ)
    (sample : Unit × input.World)
    (hno : sample ∉ retainedOverflow input C hretained accounting budget quota) (n : ℕ) :
    run input C .uncapped accounting (retainedRule input budget (some quota)) sample n =
      run input C .uncapped accounting (retainedRule input budget none) sample n := by
  rcases retainedRun_quota_coupling input C hretained accounting budget quota sample n with heq | hstopped
  · exact heq
  · exact (hno hstopped.1).elim

/-- Every actual bill through the stopping time is retained, including
payments on eventual failures and finite-paid nonreturn. Taking the supremum
does not require finiteness of either expectation. -/
theorem retainedRunActualBill_le_ideal (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (quota : I.Stage → ℕ)
    (sample : Unit × input.World) :
    runActualBill input C .uncapped accounting (retainedRule input budget (some quota)) sample ≤
      runActualBill input C .uncapped accounting (retainedRule input budget none) sample := by
  apply iSup_le
  intro n
  rcases retainedRun_quota_coupling input C hretained accounting budget quota sample n with heq | hstopped
  · rw [heq]
    exact prefixBill_le_runActualBill input C .uncapped accounting _ sample n
  · obtain ⟨k, _, hk⟩ := hstopped.2
    rw [hk, stop_actualBill]
    exact prefixBill_le_runActualBill input C .uncapped accounting _ sample k

theorem retainedRisk_le_ideal_add_overflow (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (quota : I.Stage → ℕ) :
    risk input C .uncapped accounting (retainedRule input budget (some quota)) (Measure.dirac ()) ≤
      risk input C .uncapped accounting (retainedRule input budget none) (Measure.dirac ()) +
        input.seededWorldLaw (Measure.dirac ())
          (retainedOverflow input C hretained accounting budget quota) := by
  have hinclusion :
      {sample : Unit × input.World | ¬ runSuccess input C .uncapped accounting
        (retainedRule input budget (some quota)) sample} ⊆
      {sample : Unit × input.World | ¬ runSuccess input C .uncapped accounting
        (retainedRule input budget none) sample} ∪
        retainedOverflow input C hretained accounting budget quota := by
    intro sample hfailed
    by_cases ho : sample ∈ retainedOverflow input C hretained accounting budget quota
    · exact Or.inr ho
    · apply Or.inl
      intro hsuccess
      obtain ⟨n, hh, hs⟩ := hsuccess
      apply hfailed
      have heq := retainedRun_eq_of_not_overflow input C hretained accounting budget quota sample ho n
      exact ⟨n, by rw [heq]; exact hh, by rw [heq]; exact hs⟩
  exact (measure_mono hinclusion).trans (measure_union_le _ _)


end PaperProofs.Retained.PRetTruncation120

