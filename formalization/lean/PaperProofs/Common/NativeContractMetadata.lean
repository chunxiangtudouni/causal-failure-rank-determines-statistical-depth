module

public import PaperProofs.Common.NativePenalty

/-!
Only after caps have been removed, quota/H/H0 metadata no longer affect the
protocol, its policy class or its observation-plus-failure penalty value.
Reporting, irrevocable allocation and execution rights are retained exactly.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PaperProofs.Common

variable {I : Instance}

def Contract.withCaps (C : Contract I) (quota : I.Stage → ℕ) (H H0 : ℕ) : Contract I :=
  { C with reviewQuota := quota, totalCallCap := H, normalCallBound := H0 }

def currentRelaxedContract (I : Instance) : Contract I :=
  ⟨.early, .currentWindow, .terminalBarrier, fun _ => 0, 0, 0⟩

theorem currentRelaxedContract_rights (I : Instance) :
    (currentRelaxedContract I).IsCurrentAllocation ∧
      (currentRelaxedContract I).execution = .terminalBarrier := ⟨⟨rfl, rfl⟩, rfl⟩

theorem Contract.deferred_zeroCaps (C : Contract I) (hC : C.IsCurrentAllocation) :
    C.deferExecution.withCaps (fun _ => 0) 0 0 = currentRelaxedContract I := by
  cases C with
  | mk reporting allocation execution quota H H0 =>
    rcases hC with ⟨rfl, rfl⟩
    rfl

namespace Native

theorem step_recap_iff (input : StatisticalInput I) (C : Contract I)
    (quota : I.Stage → ℕ) (H H0 : ℕ) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    (s s' : State I) (action : Action I) :
    Step input C .uncapped accounting tapes s action s' ↔
      Step input (C.withCaps quota H H0) .uncapped accounting tapes s action s' := by
  constructor <;> intro h <;> cases h <;> constructor <;>
    first | assumption | exact Or.inl rfl

variable {Seed : Type*}

theorem prefix_recap_iff (input : StatisticalInput I) (C : Contract I)
    (quota : I.Stage → ℕ) (H H0 : ℕ) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) (n : ℕ) (s : State I) :
    Prefix input C .uncapped accounting policy seed truth tapes n s ↔
      Prefix input (C.withCaps quota H H0) .uncapped accounting policy seed truth tapes n s := by
  constructor <;> intro hp
  · induction hp with
    | initial => exact .initial
    | next _ hs ih => exact .next ih ((step_recap_iff input C quota H H0 accounting tapes _ _ _).mp hs)
  · induction hp with
    | initial => exact .initial
    | next _ hs ih => exact .next ih ((step_recap_iff input C quota H H0 accounting tapes _ _ _).mpr hs)

theorem legalRule_recap_iff (input : StatisticalInput I) (C : Contract I)
    (quota : I.Stage → ℕ) (H H0 : ℕ) (accounting : NormalAccounting I) (policy : PolicyRule I Seed) :
    LegalRule input C .uncapped accounting policy ↔
      LegalRule input (C.withCaps quota H H0) .uncapped accounting policy := by
  constructor <;> intro h seed truth tapes n s hp ha
  · obtain ⟨next, hs⟩ := h seed truth tapes n s
      ((prefix_recap_iff input C quota H H0 accounting policy seed truth tapes n s).mpr hp) ha
    exact ⟨next, (step_recap_iff input C quota H H0 accounting tapes _ _ _).mp hs⟩
  · obtain ⟨next, hs⟩ := h seed truth tapes n s
      ((prefix_recap_iff input C quota H H0 accounting policy seed truth tapes n s).mp hp) ha
    exact ⟨next, (step_recap_iff input C quota H H0 accounting tapes _ _ _).mpr hs⟩

theorem nextFromFrontier_recap_eq (input : StatisticalInput I) (C : Contract I)
    (quota : I.Stage → ℕ) (H H0 : ℕ) (accounting : NormalAccounting I)
    (s : State I) (action : Action I) (frontier : Frontier input) :
    nextFromFrontier input (C.withCaps quota H H0) .uncapped accounting s action frontier =
      nextFromFrontier input C .uncapped accounting s action frontier := by
  by_cases hh : s.halted = true
  · simp [nextFromFrontier, hh]
  · have ha := Bool.eq_false_iff.mpr hh
    by_cases hex : ∃ next, Step input C .uncapped accounting (frozenTapes input frontier) s action next
    · obtain ⟨next, hs⟩ := hex
      rw [nextFromFrontier_eq_of_step input C .uncapped accounting s next action frontier ha hs,
        nextFromFrontier_eq_of_step input (C.withCaps quota H H0) .uncapped accounting s next action
          frontier ha ((step_recap_iff input C quota H H0 accounting _ _ _ _).mp hs)]
    · have hex' : ¬ ∃ next, Step input (C.withCaps quota H H0) .uncapped accounting
          (frozenTapes input frontier) s action next := by
        rintro ⟨next, hs⟩
        exact hex ⟨next, (step_recap_iff input C quota H H0 accounting _ _ _ _).mpr hs⟩
      simp only [nextFromFrontier, ha, Bool.false_eq_true, ↓reduceIte, dite_eq_right hex, dite_eq_right hex']

theorem run_recap_eq (input : StatisticalInput I) (C : Contract I)
    (quota : I.Stage → ℕ) (H H0 : ℕ) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ) :
    run input (C.withCaps quota H H0) .uncapped accounting policy sample n =
      run input C .uncapped accounting policy sample n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    exact nextFromFrontier_recap_eq input C quota H H0 accounting _ _ _

theorem runSuccess_recap_iff (input : StatisticalInput I) (C : Contract I)
    (quota : I.Stage → ℕ) (H H0 : ℕ) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) :
    runSuccess input (C.withCaps quota H H0) .uncapped accounting policy sample ↔
      runSuccess input C .uncapped accounting policy sample := by
  simp only [runSuccess, run_recap_eq]
  rfl

section Measurable

variable [MeasurableSpace Seed]

def Policy.recap (input : StatisticalInput I) (C : Contract I)
    (quota : I.Stage → ℕ) (H H0 : ℕ) (accounting : NormalAccounting I)
    (policy : Policy input C .uncapped accounting Seed) :
    Policy input (C.withCaps quota H H0) .uncapped accounting Seed where
  rule := policy.rule
  measurable_rule := policy.measurable_rule
  legal := (legalRule_recap_iff input C quota H H0 accounting policy.rule).mp policy.legal

def Policy.uncapMetadata (input : StatisticalInput I) (C : Contract I)
    (quota : I.Stage → ℕ) (H H0 : ℕ) (accounting : NormalAccounting I)
    (policy : Policy input (C.withCaps quota H H0) .uncapped accounting Seed) :
    Policy input C .uncapped accounting Seed where
  rule := policy.rule
  measurable_rule := policy.measurable_rule
  legal := (legalRule_recap_iff input C quota H H0 accounting policy.rule).mpr policy.legal

theorem penaltyObjective_recap_eq (input : StatisticalInput I) (C : Contract I)
    (quota : I.Stage → ℕ) (H H0 : ℕ) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    penaltyObjective input (C.withCaps quota H H0) .uncapped accounting policy ν penalty =
      penaltyObjective input C .uncapped accounting policy ν penalty := by
  unfold penaltyObjective expectedObservationBill runObservationBill risk
  simp_rw [run_recap_eq, runSuccess_recap_iff]

end Measurable

theorem penaltyValue_recap_eq (input : StatisticalInput I) (C : Contract I)
    (quota : I.Stage → ℕ) (H H0 : ℕ) (accounting : NormalAccounting I) (penalty : ℝ≥0∞) :
    penaltyValue input (C.withCaps quota H H0) accounting penalty = penaltyValue input C accounting penalty := by
  apply le_antisymm
  · conv_rhs => unfold penaltyValue
    refine le_iInf fun SmallSeed => le_iInf fun m => ?_
    let : MeasurableSpace SmallSeed := m
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    refine le_iInf fun policy => ?_
    have h := penaltyValue_le_policy input (C.withCaps quota H H0) accounting penalty ν
      (policy.recap input C quota H H0 accounting)
    change penaltyValue input (C.withCaps quota H H0) accounting penalty ≤
      penaltyObjective input (C.withCaps quota H H0) .uncapped accounting policy.rule ν penalty at h
    rwa [penaltyObjective_recap_eq] at h
  · conv_rhs => unfold penaltyValue
    refine le_iInf fun SmallSeed => le_iInf fun m => ?_
    let : MeasurableSpace SmallSeed := m
    refine le_iInf fun ν => le_iInf fun hν => ?_
    let : IsProbabilityMeasure ν := hν
    refine le_iInf fun policy => ?_
    have h := penaltyValue_le_policy input C accounting penalty ν
      (policy.uncapMetadata input C quota H H0 accounting)
    change penaltyValue input C accounting penalty ≤
      penaltyObjective input C .uncapped accounting policy.rule ν penalty at h
    rwa [← penaltyObjective_recap_eq input C quota H H0 accounting policy.rule ν penalty] at h

theorem penaltyValue_currentContract (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (penalty : ℝ≥0∞) :
    penaltyValue input C.deferExecution accounting penalty =
      penaltyValue input (currentRelaxedContract I) accounting penalty := by
  rw [← C.deferred_zeroCaps hC, penaltyValue_recap_eq]

end Native
end PaperProofs.Common
