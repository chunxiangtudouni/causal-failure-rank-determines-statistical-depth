module

public import PaperProofs.Common.NativeRelaxation
public import PaperProofs.Common.NativeDeadlines

/-!
The comparator inclusion from current physical execution/payment to the
larger contract allowing an already allocated correction to execute later.
Only the execution deadline changes. Reports, irrevocable allocation,
original resources, accounting, channels, actual fees and private seeds stay
the same. The comparison is between genuine policy infima.

An embedded individual policy has the same actual states, risk and bill.
The optimized values are compared only by an inequality, not an equality.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common

variable {I : Instance}

def Contract.deferExecution (C : Contract I) : Contract I :=
  { C with execution := .terminalBarrier }

theorem Contract.deferExecution_fields (C : Contract I) :
    C.deferExecution.reporting = C.reporting ∧
      C.deferExecution.allocation = C.allocation ∧
      C.deferExecution.execution = .terminalBarrier ∧
      C.deferExecution.reviewQuota = C.reviewQuota ∧
      C.deferExecution.totalCallCap = C.totalCallCap ∧
      C.deferExecution.normalCallBound = C.normalCallBound :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Contract.currentPayment_defer_currentAllocation (C : Contract I)
    (h : C.IsCurrentPayment) : C.deferExecution.IsCurrentAllocation :=
  h.1

namespace Native

theorem step_to_deferred (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (h : Step input C mode accounting tapes s action s') :
    Step input C.deferExecution mode accounting tapes s action s' := by
  cases h <;> constructor <;>
    first | assumption | simp [executionOpen, Contract.deferExecution]

section Prefixes

variable {Seed : Type*}

theorem prefix_to_deferred (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (h : Prefix input C mode accounting policy seed truth tapes n s) :
    Prefix input C.deferExecution mode accounting policy seed truth tapes n s := by
  induction h with
  | initial => exact .initial
  | next _ step ih => exact .next ih (step_to_deferred input C mode accounting tapes step)

/-- Reached deferred paths of an already-legal old rule are old paths too:
the old legal next step is also deferred and hence equals the actual one. -/
theorem prefix_deferred_to_original (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (h : Prefix input C.deferExecution mode accounting policy seed truth tapes n s) :
    Prefix input C mode accounting policy seed truth tapes n s := by
  induction h with
  | initial => exact .initial
  | next _ step ih =>
    have hactive := step_source_active input C.deferExecution mode accounting tapes step
    obtain ⟨sOriginal, hnext⟩ := hlegal seed truth tapes _ _ ih hactive
    have heq := step_deterministic input C.deferExecution mode accounting tapes
      (step_to_deferred input C mode accounting tapes hnext) step
    cases heq
    exact .next ih hnext

theorem legalRule_deferred_of_original (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) :
    LegalRule input C.deferExecution mode accounting policy := by
  intro seed truth tapes n s hp hactive
  have hold := prefix_deferred_to_original input C mode accounting policy hlegal seed truth tapes hp
  obtain ⟨next, hstep⟩ := hlegal seed truth tapes n s hold hactive
  exact ⟨next, step_to_deferred input C mode accounting tapes hstep⟩

/-- Contract weakening changes no reached state of the same legal rule. -/
theorem run_deferred_eq_original (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World) (n : ℕ) :
    run input C.deferExecution mode accounting policy sample n =
      run input C mode accounting policy sample n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting policy hlegal sample n
    by_cases hhalt : (run input C mode accounting policy sample n).halted = true
    · have hhaltDeferred :
          (run input C.deferExecution mode accounting policy sample n).halted = true := by
        rw [ih]
        exact hhalt
      rw [run_succ_of_halted input C.deferExecution mode accounting policy sample n hhaltDeferred,
        run_succ_of_halted input C mode accounting policy sample n hhalt]
      exact ih
    · have hactive : (run input C mode accounting policy sample n).halted = false :=
        Bool.eq_false_iff.mpr hhalt
      obtain ⟨next, hnext⟩ := hlegal sample.1 (input.truthAt sample.2)
        (worldTapes input sample.2) m _ hp hactive
      have hactiveDeferred :
          (run input C.deferExecution mode accounting policy sample n).halted = false := by
        rw [ih]
        exact hactive
      have hnextDeferred : Step input C.deferExecution mode accounting (worldTapes input sample.2)
          (run input C.deferExecution mode accounting policy sample n)
          (policy sample.1 (run input C.deferExecution mode accounting policy sample n).history) next := by
        rw [ih]
        exact step_to_deferred input C mode accounting _ hnext
      rw [run_succ_of_step input C.deferExecution mode accounting policy sample n next
        hactiveDeferred hnextDeferred,
        run_succ_of_step input C mode accounting policy sample n next hactive hnext]

theorem run_schedule_deferred_eq_original (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World) :
    run input C.deferExecution mode accounting policy sample =
      run input C mode accounting policy sample :=
  funext (run_deferred_eq_original input C mode accounting policy hlegal sample)

/-- Different contract success predicates agree on this embedded actual
execution because both have been proved equivalent to physical correctness. -/
theorem runSuccess_deferred_iff_original (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World) :
    runSuccess input C.deferExecution mode accounting policy sample ↔
      runSuccess input C mode accounting policy sample := by
  have hlegalDeferred := legalRule_deferred_of_original input C mode accounting policy hlegal
  constructor
  · rintro ⟨n, hhalt, hsuccess⟩
    refine ⟨n, ?_, ?_⟩
    · rw [run_deferred_eq_original input C mode accounting policy hlegal sample n] at hhalt
      exact hhalt
    · apply (run_success_iff_physical input C mode accounting policy hlegal sample n).mpr
      have hphysical := (run_success_iff_physical input C.deferExecution mode accounting
        policy hlegalDeferred sample n).mp hsuccess
      rwa [run_deferred_eq_original input C mode accounting policy hlegal sample n] at hphysical
  · rintro ⟨n, hhalt, hsuccess⟩
    refine ⟨n, ?_, ?_⟩
    · rw [run_deferred_eq_original input C mode accounting policy hlegal sample n]
      exact hhalt
    · apply (run_success_iff_physical input C.deferExecution mode accounting
        policy hlegalDeferred sample n).mpr
      rw [run_deferred_eq_original input C mode accounting policy hlegal sample n]
      exact (run_success_iff_physical input C mode accounting policy hlegal sample n).mp hsuccess

theorem runActualBill_deferred_eq_original (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World) :
    runActualBill input C.deferExecution mode accounting policy sample =
      runActualBill input C mode accounting policy sample :=
  congrArg (fun schedule : ℕ → State I => ⨆ n, (schedule n).ledger.actualBill input.fees)
    (run_schedule_deferred_eq_original input C mode accounting policy hlegal sample)

end Prefixes

section MeasurableSeed

variable {Seed : Type*} [MeasurableSpace Seed]

theorem risk_deferred_eq_original (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (ν : Measure Seed) :
    risk input C.deferExecution mode accounting policy ν = risk input C mode accounting policy ν := by
  apply congrArg (fun event : Set (Seed × input.World) => input.seededWorldLaw ν event)
  apply Set.ext
  intro sample
  exact not_congr (runSuccess_deferred_iff_original input C mode accounting policy hlegal sample)

theorem expectedBill_deferred_eq_original (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (ν : Measure Seed) :
    expectedBill input C.deferExecution mode accounting policy ν =
      expectedBill input C mode accounting policy ν := by
  apply congrArg (fun bill : (Seed × input.World) → ℝ≥0∞ =>
    ∫⁻ sample, bill sample ∂input.seededWorldLaw ν)
  exact funext (runActualBill_deferred_eq_original input C mode accounting policy hlegal)

def Policy.deferExecution (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed) :
    Policy input C.deferExecution mode accounting Seed where
  rule := policy.rule
  measurable_rule := policy.measurable_rule
  legal := legalRule_deferred_of_original input C mode accounting policy.rule policy.legal

end MeasurableSeed

/-- Only a comparator inequality is asserted; the enlarged contract may
have genuinely better policies at finite risk. The seed universe is Type 0,
as in the already-defined actual-policy value. -/
theorem value_deferred_le_original (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (δ : ℝ≥0∞) :
    value input C.deferExecution mode accounting δ ≤ value input C mode accounting δ := by
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  let deferred := Policy.deferExecution input C mode accounting policy.val
  have hrisk : risk input C.deferExecution mode accounting deferred.rule ν ≤ δ := by
    change risk input C.deferExecution mode accounting policy.val.rule ν ≤ δ
    rw [risk_deferred_eq_original input C mode accounting policy.val.rule policy.val.legal ν]
    exact policy.property
  calc
    _ ≤ expectedBill input C.deferExecution mode accounting deferred.rule ν :=
      value_le_policy input C.deferExecution mode accounting δ ν deferred hrisk
    _ = expectedBill input C mode accounting policy.val.rule ν :=
      expectedBill_deferred_eq_original input C mode accounting policy.val.rule policy.val.legal ν

end Native

end PaperProofs.Common
