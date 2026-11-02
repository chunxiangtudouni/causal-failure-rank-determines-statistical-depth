module

public import PaperProofs.Paid.PenaltyProgram
public import PaperProofs.Common.NativeBellmanSuccessLift
public import PaperProofs.Common.NativeBellmanGuardLift
public import PaperProofs.Common.FreshSuffixComposition

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

/-- The charge of visible ACTUAL executions. Allocated-but-unexecuted rights
are absent, and no success condition removes failed-path payments. -/
noncomputable def historyCorrectionCharge (input : StatisticalInput I) (history : List (VisibleEvent I)) : ℝ≥0∞ :=
  ((historyExecutions history).map (fun pair => ENNReal.ofReal (input.fees.correction pair.1.stage pair.2 : ℝ))).sum

theorem prefix_correctionBill_eq_historyCharge {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (hp : Prefix input C mode accounting rule seed truth tapes n state) :
    state.ledger.correctionBill input.fees = historyCorrectionCharge input state.history := by
  simp only [historyCorrectionCharge,
    prefix_historyExecutions input C mode accounting rule seed truth tapes hp, List.map_map,
    Ledger.correctionBill]
  rfl

theorem historyCorrectionCharge_suffixJoin (input : StatisticalInput I) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first))) :
    historyCorrectionCharge input (referenceSuffixHistoryJoin I first before after) =
      historyCorrectionCharge input before + historyCorrectionCharge (input.freshSuffix first) after := by
  unfold historyCorrectionCharge
  rw [GuardLift.historyExecutions_referenceSuffixJoin, List.map_append, List.sum_append, List.map_map]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair _hpair
  change ENNReal.ofReal (input.correctionFee (I.freshStageLift first pair.1.stage) pair.2 : ℝ) =
    ENNReal.ofReal ((input.freshSuffix first).correctionFee pair.1.stage pair.2 : ℝ)
  exact congrArg (fun charge : ℚ => ENNReal.ofReal (charge : ℝ))
    (input.freshSuffix_correctionFee first pair.1.stage pair.2).symm

/-- Exact actual-correction-cost decomposition on a genuine parent/child
prefix view. It includes every already-paid old fee and all child fees. -/
theorem correctionBill_suffixView {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (childC : Contract (I.freshSuffix first)) (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (childTruth : (I.freshSuffix first).Stage → Bool) (childTapes : ReviewTapes (input.freshSuffix first))
    {parentClock childClock : ℕ} {parent : State I} {child : State (I.freshSuffix first)}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes parentClock parent)
    (hc : Prefix (input.freshSuffix first) childC .uncapped childAccounting childRule seed childTruth childTapes childClock child)
    (before : List (VisibleEvent I)) (view : ReferenceSuffixView I first before parent child) :
    parent.ledger.correctionBill input.fees = historyCorrectionCharge input before +
      child.ledger.correctionBill (input.freshSuffix first).fees := by
  rw [prefix_correctionBill_eq_historyCharge input C .uncapped accounting rule seed truth tapes hp,
    view.history, historyCorrectionCharge_suffixJoin,
    ← prefix_correctionBill_eq_historyCharge (input.freshSuffix first) childC .uncapped childAccounting childRule
      seed childTruth childTapes hc]

noncomputable def runPaidPenaltyCharge {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (penalty : ℝ≥0∞)
    (sample : Seed × input.World) : ℝ≥0∞ := by
  classical
  exact runActualBill input C .uncapped accounting rule sample +
    if runSuccess input C .uncapped accounting rule sample then 0 else penalty

theorem measurable_runPaidPenaltyCharge {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (penalty : ℝ≥0∞) :
    Measurable (runPaidPenaltyCharge input C accounting rule penalty) := by
  classical
  exact (measurable_runActualBill input C .uncapped accounting rule hm).add
    (Measurable.ite (measurableSet_runSuccess input C .uncapped accounting rule hm) measurable_const measurable_const)

theorem paidPenaltyObjective_eq_lintegral {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (ν : Measure Seed) (penalty : ℝ≥0∞) :
    paidPenaltyObjective input C accounting rule ν penalty =
      ∫⁻ sample, runPaidPenaltyCharge input C accounting rule penalty sample ∂input.seededWorldLaw ν := by
  classical
  have hfail : MeasurableSet {sample : Seed × input.World | ¬ runSuccess input C .uncapped accounting rule sample} :=
    (measurableSet_runSuccess input C .uncapped accounting rule hm).compl
  have heq : (fun sample => runPaidPenaltyCharge input C accounting rule penalty sample) =
      fun sample => runActualBill input C .uncapped accounting rule sample +
        {sample | ¬ runSuccess input C .uncapped accounting rule sample}.indicator (fun _ => penalty) sample := by
    funext sample
    by_cases hs : runSuccess input C .uncapped accounting rule sample <;>
      simp only [runPaidPenaltyCharge, hs, ite_true, ite_false, Set.indicator, Set.mem_ofPred_eq,
        not_true_eq_false, not_false_eq_true]
  rw [heq, lintegral_add_left (measurable_runActualBill input C .uncapped accounting rule hm),
    lintegral_indicator_const hfail]
  rfl

end PDMenu
