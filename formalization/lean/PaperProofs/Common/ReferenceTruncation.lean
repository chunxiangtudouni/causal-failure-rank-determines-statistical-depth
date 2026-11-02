module

public import PaperProofs.Common.ReferenceCertification
public import PaperProofs.Common.ReferenceControllerQuota

/-! Same-tape coupling of the actual ideal and quota-truncated reference rules.
No success or finite-cost event is selected. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance}

theorem referenceTestingAction_quota_coupling (input : StatisticalInput I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (cache : ReferenceReplayCache I) (stage : I.Stage) :
    referenceTestingAction input available budget (some quota) cache stage =
      referenceTestingAction input available budget none cache stage ∨
    (referenceTestingAction input available budget none cache stage = .review stage ∧
      quota stage ≤ (historyObservations cache.seen stage).length ∧
      referenceTestingAction input available budget (some quota) cache stage = .abandon) := by
  cases hk : referenceAvailableKind I available cache with
  | none => exact Or.inl (by simp [referenceTestingAction, hk])
  | some kind =>
    cases kind with
    | infiniteRank => exact Or.inl (by simp [referenceTestingAction, hk])
    | noTool | finiteBad depth =>
      cases ht : referenceAvailableCacheTarget I available budget cache with
      | none => exact Or.inl (by simp [referenceTestingAction, hk, ht])
      | some target =>
        by_cases hv : ∀ symbol ∈ historyObservations cache.seen stage,
            symbol < (input.experiment stage).alphabetSize
        · simp only [referenceTestingAction, hk, ht, dite_eq_left hv]
          by_cases hh : (input.experiment stage).rationalWordHits target
              (historyObservationWord input cache.seen stage hv) = true
          · exact Or.inl (by simp only [hh, ite_true])
          · simp only [ite_eq_right hh]
            by_cases hq : (historyObservations cache.seen stage).length < quota stage
            · exact Or.inl (by simp only [ite_eq_left hq])
            · exact Or.inr ⟨trivial, Nat.le_of_not_lt hq, by simp only [ite_eq_right hq]⟩
        · exact Or.inl (by simp only [referenceTestingAction, hk, ht, dite_eq_right hv])

theorem referenceCandidateAction_quota_coupling (input : StatisticalInput I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (history : List (VisibleEvent I)) :
    referenceCandidateAction input available budget (some quota) history =
      referenceCandidateAction input available budget none history ∨
    ∃ stage : I.Stage,
      referenceCandidateAction input available budget none history = .review stage ∧
      quota stage ≤ (historyObservations history stage).length ∧
      referenceCandidateAction input available budget (some quota) history = .abandon := by
  cases hp : referenceAvailableReplay input available budget history with
  | none => exact Or.inl (by simp [referenceCandidateAction, hp])
  | some cache =>
    cases hh : cache.halted with
    | true => exact Or.inl (by simp [referenceCandidateAction, hp, hh])
    | false =>
      cases hs : referenceReplayStage I cache with
      | none => exact Or.inl (by simp [referenceCandidateAction, hp, hh, hs])
      | some stage =>
        cases hphase : cache.phase with
        | written | reported | allocated tool | executed tool =>
          exact Or.inl (by simp [referenceCandidateAction, hp, hh, hs, hphase])
        | testing =>
          have hseen := (referenceAvailableReplay_some_spec input available budget history cache hp).2.2.2.2.2
          rcases referenceTestingAction_quota_coupling input available budget quota cache stage with hsame | hdiff
          · exact Or.inl (by simpa only [referenceCandidateAction, hp, hh, Bool.false_eq_true,
              ite_false, hs, hphase] using hsame)
          · refine Or.inr ⟨stage, ?_, ?_, ?_⟩
            · simpa only [referenceCandidateAction, hp, hh, Bool.false_eq_true, ite_false, hs, hphase] using hdiff.1
            · simpa only [hseen] using hdiff.2.1
            · simpa only [referenceCandidateAction, hp, hh, Bool.false_eq_true, ite_false, hs, hphase] using hdiff.2.2

theorem referenceRule_quota_coupling {Seed : Type*} (input : StatisticalInput I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (seed : Seed) (history : List (VisibleEvent I)) :
    referenceRule input available budget (some quota) seed history =
      referenceRule input available budget none seed history ∨
    ∃ stage : I.Stage,
      referenceRule input available budget none seed history = .review stage ∧
      quota stage ≤ (historyObservations history stage).length ∧
      referenceRule input available budget (some quota) seed history = .abandon := by
  rcases referenceCandidateAction_quota_coupling input available budget quota history with hsame | ⟨stage, hi, hq, hb⟩
  · exact Or.inl (by simp only [referenceRule, hsame])
  · by_cases ha : historyAllowsAction history (referenceCandidateAction input available budget none history)
    · refine Or.inr ⟨stage, ?_, hq, ?_⟩
      · simpa only [referenceRule, ite_eq_left ha] using hi
      · simp only [referenceRule, hb, historyAllowsAction, ↓reduceIte]
    · have hiRule : referenceRule input available budget none seed history = .abandon :=
        ite_eq_right ha
      have hbRule : referenceRule input available budget (some quota) seed history = .abandon := by
        simp only [referenceRule, hb, historyAllowsAction, ↓reduceIte]
      exact Or.inl (hbRule.trans hiRule.symm)

/-- At every interpreter time the two paths still coincide, or the bounded
path has abandoned at one earlier ideal state. That state witnesses actual
overflow, and its entire old ledger remains present. -/
theorem referenceRun_quota_coupling (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (sample : Unit × input.World) (n : ℕ) :
    let ideal := referenceRule (Seed := Unit) input available budget none
    let bounded := referenceRule (Seed := Unit) input available budget (some quota)
    run input C .uncapped accounting bounded sample n = run input C .uncapped accounting ideal sample n ∨
      (sample ∈ referenceOverflow input C hearly accounting available budget quota ∧
        ∃ k < n, run input C .uncapped accounting bounded sample n =
          stopState (run input C .uncapped accounting ideal sample k) true) := by
  let ideal := referenceRule (Seed := Unit) input available budget none
  let bounded := referenceRule (Seed := Unit) input available budget (some quota)
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
        rcases referenceRule_quota_coupling input available budget quota sample.1
            (run input C .uncapped accounting ideal sample n).history with hsame | ⟨stage, hi, hq, hb⟩
        · exact Or.inl (by
            simp only [run]
            rw [heq]
            change nextFromFrontier input C .uncapped accounting _
              (referenceRule input available budget (some quota) sample.1 _) _ = _
            rw [hsame])
        · have hidealLegal : LegalRule input C .uncapped accounting ideal :=
            referenceRule_uncapped_legal input C hearly accounting available budget none
          obtain ⟨prefixLength, _, hp⟩ := run_has_prefix input C .uncapped accounting ideal hidealLegal sample n
          have hqledger : (quota stage : ℕ∞) ≤ (run input C .uncapped accounting ideal sample n).ledger.reviews stage := by
            rw [← prefix_historyObservations_length input C .uncapped accounting ideal sample.1
              (input.truthAt sample.2) (worldTapes input sample.2) hp stage]
            exact_mod_cast hq
          have ho : sample ∈ referenceOverflow input C hearly accounting available budget quota :=
            ⟨n, stage, hactive, hi, hqledger⟩
          have hactiveb : (run input C .uncapped accounting bounded sample n).halted = false := by rw [heq]; exact hactive
          have hstep : Step input C .uncapped accounting (worldTapes input sample.2)
              (run input C .uncapped accounting bounded sample n)
              (bounded sample.1 (run input C .uncapped accounting bounded sample n).history)
              (stopState (run input C .uncapped accounting ideal sample n) true) := by
            rw [heq]
            change Step input C .uncapped accounting _ _
              (referenceRule input available budget (some quota) sample.1 _) _
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

theorem referenceRun_eq_of_not_overflow (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (sample : Unit × input.World)
    (hno : sample ∉ referenceOverflow input C hearly accounting available budget quota) (n : ℕ) :
    run input C .uncapped accounting (referenceRule input available budget (some quota)) sample n =
      run input C .uncapped accounting (referenceRule input available budget none) sample n := by
  rcases referenceRun_quota_coupling input C hearly accounting available budget quota sample n with heq | hstopped
  · exact heq
  · exact (hno hstopped.1).elim

/-- Every actual bill through the stopping time is retained, including
payments on eventual failures and finite-paid nonreturn. Taking the supremum
does not require finiteness of either expectation. -/
theorem referenceRunActualBill_le_ideal (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (sample : Unit × input.World) :
    runActualBill input C .uncapped accounting (referenceRule input available budget (some quota)) sample ≤
      runActualBill input C .uncapped accounting (referenceRule input available budget none) sample := by
  apply iSup_le
  intro n
  rcases referenceRun_quota_coupling input C hearly accounting available budget quota sample n with heq | hstopped
  · rw [heq]
    exact prefixBill_le_runActualBill input C .uncapped accounting _ sample n
  · obtain ⟨k, _, hk⟩ := hstopped.2
    rw [hk, stop_actualBill]
    exact prefixBill_le_runActualBill input C .uncapped accounting _ sample k

theorem referenceRisk_le_ideal_add_overflow (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ) :
    risk input C .uncapped accounting (referenceRule input available budget (some quota)) (Measure.dirac ()) ≤
      risk input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) +
        input.seededWorldLaw (Measure.dirac ())
          (referenceOverflow input C hearly accounting available budget quota) := by
  have hinclusion :
      {sample : Unit × input.World | ¬ runSuccess input C .uncapped accounting
        (referenceRule input available budget (some quota)) sample} ⊆
      {sample : Unit × input.World | ¬ runSuccess input C .uncapped accounting
        (referenceRule input available budget none) sample} ∪
        referenceOverflow input C hearly accounting available budget quota := by
    intro sample hfailed
    by_cases ho : sample ∈ referenceOverflow input C hearly accounting available budget quota
    · exact Or.inr ho
    · apply Or.inl
      intro hsuccess
      obtain ⟨n, hh, hs⟩ := hsuccess
      apply hfailed
      have heq := referenceRun_eq_of_not_overflow input C hearly accounting available budget quota sample ho n
      exact ⟨n, by rw [heq]; exact hh, by rw [heq]; exact hs⟩
  exact (measure_mono hinclusion).trans (measure_union_le _ _)

/-- The original B22 target is closed for the unchanged actual controller.
The proof is stronger than its numerical-quota instance: the same coupling
works for every per-stage quota, including zero. -/
theorem referenceTruncationGuarantee (input : StatisticalInput I) :
    ReferenceTruncationGuarantee input := by
  intro C hearly accounting available budget exponent _hpositive _hsmall
  exact ⟨referenceRunActualBill_le_ideal input C hearly accounting available budget (referenceQuota input exponent),
    referenceRun_eq_of_not_overflow input C hearly accounting available budget (referenceQuota input exponent),
    referenceRisk_le_ideal_add_overflow input C hearly accounting available budget (referenceQuota input exponent)⟩

end PaperProofs.Common.Native
