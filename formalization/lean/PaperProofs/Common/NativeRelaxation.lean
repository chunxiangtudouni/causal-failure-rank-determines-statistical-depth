module

public import PaperProofs.Common.NativeRun

/-!
Relaxing only native resource caps preserves every already-legal policy's
actual execution. Input, channel laws, accounting, reporting, allocation,
execution/payment deadlines, private seed, and rule remain identical.

The legal-rule inclusion is proved via deterministic protocol prefixes;
run equality is then derived from real legal steps. It is not assumed as
a premise of the value comparison. Expectations remain ENNReal, including
infinite actual bills.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem step_native_to_uncapped (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (h : Step input C .native accounting tapes s action s') :
    Step input C .uncapped accounting tapes s action s' := by
  cases h <;> constructor <;> first | assumption | exact Or.inl rfl

theorem step_source_active (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (h : Step input C mode accounting tapes s action s') : s.halted = false := by
  cases h with
  | review _ live _ _ => exact live.1
  | write _ _ live _ _ => exact live.1
  | allocate _ _ active _ _ _ _ _ _ => exact active
  | execute _ _ active _ _ _ _ _ _ _ => exact active
  | advance _ live _ _ => exact live.1
  | stop active => exact active
  | abandon active => exact active

section Prefixes

variable {Seed : Type*}

theorem prefix_native_to_uncapped (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (h : Prefix input C .native accounting policy seed truth tapes n s) :
    Prefix input C .uncapped accounting policy seed truth tapes n s := by
  induction h with
  | initial => exact .initial
  | next _ step ih => exact .next ih (step_native_to_uncapped input C accounting tapes step)

/-- Extra uncapped transitions cannot create a new reached path for a rule
that was already legal with caps: its native next step exists and is the
same uncapped next step by protocol determinism. -/
theorem prefix_uncapped_to_native (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting policy) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (h : Prefix input C .uncapped accounting policy seed truth tapes n s) :
    Prefix input C .native accounting policy seed truth tapes n s := by
  induction h with
  | initial => exact .initial
  | next _ step ih =>
    have hactive := step_source_active input C .uncapped accounting tapes step
    obtain ⟨sNative, hnext⟩ := hlegal seed truth tapes _ _ ih hactive
    have heq := step_deterministic input C .uncapped accounting tapes
      (step_native_to_uncapped input C accounting tapes hnext) step
    cases heq
    exact .next ih hnext

theorem legalRule_uncapped_of_native (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting policy) :
    LegalRule input C .uncapped accounting policy := by
  intro seed truth tapes n s hp hactive
  have hnative := prefix_uncapped_to_native input C accounting policy hlegal seed truth tapes hp
  obtain ⟨next, hstep⟩ := hlegal seed truth tapes n s hnative hactive
  exact ⟨next, step_native_to_uncapped input C accounting tapes hstep⟩

end Prefixes

section Executions

variable {Seed : Type*}

/-- Same rule, seed and world give identical states at every interpreter
time. Native legality prevents use of either invalid-action completion. -/
theorem run_uncapped_eq_native (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting policy) (sample : Seed × input.World)
    (n : ℕ) :
    run input C .uncapped accounting policy sample n =
      run input C .native accounting policy sample n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨m, _, hp⟩ := run_has_prefix input C .native accounting policy hlegal sample n
    by_cases hhalt : (run input C .native accounting policy sample n).halted = true
    · have hhaltUncapped : (run input C .uncapped accounting policy sample n).halted = true := by
        rw [ih]
        exact hhalt
      rw [run_succ_of_halted input C .uncapped accounting policy sample n hhaltUncapped,
        run_succ_of_halted input C .native accounting policy sample n hhalt]
      exact ih
    · have hactive : (run input C .native accounting policy sample n).halted = false :=
        Bool.eq_false_iff.mpr hhalt
      obtain ⟨next, hnext⟩ := hlegal sample.1 (input.truthAt sample.2)
        (worldTapes input sample.2) m _ hp hactive
      have hactiveUncapped :
          (run input C .uncapped accounting policy sample n).halted = false := by
        rw [ih]
        exact hactive
      have hnextUncapped : Step input C .uncapped accounting (worldTapes input sample.2)
          (run input C .uncapped accounting policy sample n)
          (policy sample.1 (run input C .uncapped accounting policy sample n).history) next := by
        rw [ih]
        exact step_native_to_uncapped input C accounting _ hnext
      rw [run_succ_of_step input C .uncapped accounting policy sample n next
        hactiveUncapped hnextUncapped,
        run_succ_of_step input C .native accounting policy sample n next hactive hnext]

theorem run_schedule_uncapped_eq_native (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting policy) (sample : Seed × input.World) :
    run input C .uncapped accounting policy sample =
      run input C .native accounting policy sample :=
  funext (run_uncapped_eq_native input C accounting policy hlegal sample)

theorem runSuccess_uncapped_iff_native (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting policy) (sample : Seed × input.World) :
    runSuccess input C .uncapped accounting policy sample ↔
      runSuccess input C .native accounting policy sample := by
  unfold runSuccess
  rw [run_schedule_uncapped_eq_native input C accounting policy hlegal sample]

theorem runActualBill_uncapped_eq_native (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting policy) (sample : Seed × input.World) :
    runActualBill input C .uncapped accounting policy sample =
      runActualBill input C .native accounting policy sample :=
  congrArg (fun schedule : ℕ → State I => ⨆ n, (schedule n).ledger.actualBill input.fees)
    (run_schedule_uncapped_eq_native input C accounting policy hlegal sample)

variable [MeasurableSpace Seed]

theorem risk_uncapped_eq_native (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting policy) (ν : Measure Seed) :
    risk input C .uncapped accounting policy ν = risk input C .native accounting policy ν := by
  apply congrArg (fun event : Set (Seed × input.World) => input.seededWorldLaw ν event)
  apply Set.ext
  intro sample
  exact not_congr (runSuccess_uncapped_iff_native input C accounting policy hlegal sample)

theorem expectedBill_uncapped_eq_native (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting policy) (ν : Measure Seed) :
    expectedBill input C .uncapped accounting policy ν =
      expectedBill input C .native accounting policy ν := by
  apply congrArg (fun bill : (Seed × input.World) → ℝ≥0∞ =>
    ∫⁻ sample, bill sample ∂input.seededWorldLaw ν)
  exact funext (runActualBill_uncapped_eq_native input C accounting policy hlegal)

/-- Admissibility changes only by the proved cap-relaxation inclusion. -/
def Policy.relax (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (policy : Policy input C .native accounting Seed) :
    Policy input C .uncapped accounting Seed where
  rule := policy.rule
  measurable_rule := policy.measurable_rule
  legal := legalRule_uncapped_of_native input C accounting policy.rule policy.legal

end Executions

/-- The value's seed universe is deliberately the same Type 0 as `value`. -/
theorem value_le_policy (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (δ : ℝ≥0∞) {Seed : Type} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : Policy input C mode accounting Seed) (hrisk : risk input C mode accounting policy.rule ν ≤ δ) :
    value input C mode accounting δ ≤ expectedBill input C mode accounting policy.rule ν := by
  exact iInf_le_of_le Seed (iInf_le_of_le ‹MeasurableSpace Seed›
    (iInf_le_of_le ν (iInf_le_of_le ‹IsProbabilityMeasure ν›
      (iInf_le_of_le ⟨policy, hrisk⟩ le_rfl))))

/-- Genuine comparator inclusion for the actual same-contract native values. -/
theorem value_uncapped_le_native (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (δ : ℝ≥0∞) :
    value input C .uncapped accounting δ ≤ value input C .native accounting δ := by
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  let relaxed := Policy.relax input C accounting policy.val
  have hrisk : risk input C .uncapped accounting relaxed.rule ν ≤ δ := by
    change risk input C .uncapped accounting policy.val.rule ν ≤ δ
    rw [risk_uncapped_eq_native input C accounting policy.val.rule policy.val.legal ν]
    exact policy.property
  calc
    _ ≤ expectedBill input C .uncapped accounting relaxed.rule ν :=
      value_le_policy input C .uncapped accounting δ ν relaxed hrisk
    _ = expectedBill input C .native accounting policy.val.rule ν :=
      expectedBill_uncapped_eq_native input C accounting policy.val.rule policy.val.legal ν

end PaperProofs.Common.Native
