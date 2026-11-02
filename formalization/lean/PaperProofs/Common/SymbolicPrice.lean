module

public import PaperProofs.Statistics.Coefficient
public import PaperProofs.Structure.RankEvaluator
public import PaperProofs.Structure.IndexedQuery

/-!
Exact finite symbolic output for the frozen computable-price corollary.
The executable selector compares only integer game ranks. Rational channel
data are copied into a log-expression tree; no real KL value is queried.
The generic selector below makes no polynomial-time claim. The laminar RAM
and actual causal-controller realization remain separate L01 obligations.
-/

@[expose] public section

open scoped BigOperators

namespace PaperProofs.Common.SymbolicPrice

open PaperProofs.Statistics PaperProofs.Structure

-- Use the finite computable max/order, rather than the noncomputable
-- complete-lattice instance used elsewhere for arbitrary suprema.
local instance : SemilatticeSup ℕ∞ := (@LinearOrder.toLattice ℕ∞ instLinearOrderENat).toSemilatticeSup
local instance : OrderBot ℕ∞ := instOrderBotENat

inductive Expr where
  | rational (value : ℚ)
  | add (left right : Expr)
  | multiply (left right : Expr)
  | divide (left right : Expr)
  | log (argument : Expr)
  deriving DecidableEq

noncomputable def Expr.eval : Expr → ℝ
  | .rational value => value
  | .add left right => left.eval + right.eval
  | .multiply left right => left.eval * right.eval
  | .divide left right => left.eval / right.eval
  | .log argument => Real.log argument.eval

def sumExpr : List Expr → Expr
  | [] => .rational 0
  | head :: later => .add head (sumExpr later)

theorem eval_sumExpr (expressions : List Expr) :
    (sumExpr expressions).eval = (expressions.map Expr.eval).sum := by
  induction expressions with
  | nil => simp only [sumExpr, Expr.eval, Rat.cast_zero, List.map_nil, List.sum_nil]
  | cons head later ih => simpa only [sumExpr, Expr.eval, List.map_cons, List.sum_cons] using congrArg (head.eval + ·) ih

def divergenceExpr (E : BinaryExperiment) (x : Bool) : Expr :=
  sumExpr (List.ofFn (fun y : Fin E.alphabetSize =>
    .multiply (.rational (E.channel x y))
      (.log (.divide (.rational (E.channel x y)) (.rational (E.channel (!x) y))))))

theorem divergenceExpr_eval (E : BinaryExperiment) (x : Bool) :
    (divergenceExpr E x).eval = E.divergence x := by
  simp only [divergenceExpr, eval_sumExpr, List.map_ofFn]
  change (List.ofFn (fun y : Fin E.alphabetSize => E.channelReal x y *
    Real.log (E.channelReal x y / E.channelReal (!x) y))).sum = _
  rw [List.sum_ofFn]
  rfl

def localCoefficientExpr (E : BinaryExperiment) : Expr :=
  .multiply (.rational E.observationFee)
    (.add (.divide (.rational (E.prior false)) (divergenceExpr E false))
      (.divide (.rational (E.prior true)) (divergenceExpr E true)))

theorem localCoefficientExpr_eval (E : BinaryExperiment) :
    (localCoefficientExpr E).eval = E.coefficient := by
  simp only [localCoefficientExpr, Expr.eval, divergenceExpr_eval, BinaryExperiment.coefficient]
  congr 1
  simp only [Fintype.sum_bool, BinaryExperiment.priorReal]
  exact add_comm _ _

abbrev ExperimentSchedule (Tool : Type*) := List (Finset Tool × BinaryExperiment)

def compatibility {Tool : Type*} (stages : ExperimentSchedule Tool) : List (Finset Tool) := stages.map Prod.fst

noncomputable def weights {Tool : Type*} (stages : ExperimentSchedule Tool) : WeightedSchedule Tool :=
  stages.map (fun stage => (stage.1, stage.2.coefficient))

theorem weights_cons {Tool : Type*} (eligible : Finset Tool) (E : BinaryExperiment)
    (later : ExperimentSchedule Tool) :
    weights ((eligible, E) :: later) = (eligible, E.coefficient) :: weights later := rfl

theorem weights_eligibility {Tool : Type*} (stages : ExperimentSchedule Tool) :
    eligibilitySchedule (weights stages) = compatibility stages := by
  simp only [weights, eligibilitySchedule, compatibility, List.map_map, Function.comp_def]

def executableBadRank {Tool : Type*} [DecidableEq Tool] (eligible : Finset Tool)
    (later : ExperimentSchedule Tool) (remaining : Finset Tool) : ℕ∞ :=
  (eligible ∩ remaining).sup (fun tool => genericRank (compatibility later) (remaining.erase tool))

theorem executableBadRank_eq {Tool : Type*} [DecidableEq Tool] (eligible : Finset Tool)
    (later : ExperimentSchedule Tool) (remaining : Finset Tool) :
    executableBadRank eligible later remaining = badChildRank eligible (compatibility later) remaining := by
  simp only [executableBadRank, genericRank_eq_errorRank, badChildRank]

/-- Original ordered stage indices; duplicated channels remain distinct
stages. Selection reads only compatibility and integer ranks. -/
def heads {Tool : Type*} [DecidableEq Tool] :
    ExperimentSchedule Tool → Finset Tool → ℕ∞ → ℕ → List (ℕ × BinaryExperiment)
  | [], _, _, _ => []
  | (eligible, E) :: later, remaining, target, offset =>
      if executableBadRank eligible later remaining + 1 = target then
        (offset, E) :: heads later remaining target (offset + 1)
      else heads later remaining target (offset + 1)

def headExpression {Tool : Type*} [DecidableEq Tool] (stages : ExperimentSchedule Tool)
    (remaining : Finset Tool) (target : ℕ∞) : Expr :=
  sumExpr ((heads stages remaining target 0).map (fun head => localCoefficientExpr head.2))

theorem heads_eval {Tool : Type*} [DecidableEq Tool] (stages : ExperimentSchedule Tool)
    (remaining : Finset Tool) (target : ℕ∞) (offset : ℕ) :
    (sumExpr ((heads stages remaining target offset).map (fun head => localCoefficientExpr head.2))).eval =
      criticalHeadSum (weights stages) remaining target := by
  induction stages generalizing offset with
  | nil => simp only [heads, List.map_nil, sumExpr, Expr.eval, Rat.cast_zero, weights, criticalHeadSum]
  | cons stage later ih =>
    rcases stage with ⟨eligible, E⟩
    by_cases h : badChildRank eligible (compatibility later) remaining + 1 = target
    · simp only [heads, executableBadRank_eq, h, ite_true, List.map_cons, sumExpr, Expr.eval,
        localCoefficientExpr_eval, ih, weights_cons, criticalHeadSum, weights_eligibility]
    · simp only [heads, executableBadRank_eq, h, ite_false, ih, weights_cons,
        criticalHeadSum, weights_eligibility]
      simp only [zero_add]

def leadingExpression {Tool : Type*} [DecidableEq Tool] (stages : ExperimentSchedule Tool)
    (remaining : Finset Tool) : Expr :=
  if genericRank (compatibility stages) remaining = ⊤ then .rational 0
  else headExpression stages remaining (genericRank (compatibility stages) remaining)

theorem leadingExpression_eval {Tool : Type*} [DecidableEq Tool]
    (stages : ExperimentSchedule Tool) (remaining : Finset Tool) :
    (leadingExpression stages remaining).eval = Statistics.orderedCoefficient (weights stages) remaining := by
  by_cases htop : errorRank (compatibility stages) remaining = ⊤
  · rw [leadingExpression, genericRank_eq_errorRank, ite_eq_left htop]
    simpa only [Expr.eval, Rat.cast_zero] using
      (Statistics.orderedCoefficient_of_infiniteRank (weights stages) remaining
        (by simpa only [weights_eligibility] using htop)).symm
  · rw [leadingExpression, genericRank_eq_errorRank, ite_eq_right htop, headExpression, heads_eval,
      Statistics.orderedCoefficient_head_formula (weights stages) remaining
        (by simpa only [weights_eligibility] using htop), weights_eligibility]

theorem heads_length_le {Tool : Type*} [DecidableEq Tool] (stages : ExperimentSchedule Tool)
    (remaining : Finset Tool) (target : ℕ∞) (offset : ℕ) :
    (heads stages remaining target offset).length ≤ stages.length := by
  induction stages generalizing offset with
  | nil => exact le_rfl
  | cons stage later ih =>
    rcases stage with ⟨eligible, E⟩
    simp only [heads, List.length_cons]
    split
    · simpa only [List.length_cons] using Nat.succ_le_succ (ih (offset + 1))
    · exact (ih (offset + 1)).trans (Nat.le_succ _)

end PaperProofs.Common.SymbolicPrice

namespace PaperProofs.Common.SymbolicPrice

variable {I : Instance}

open PaperProofs.Statistics PaperProofs.Structure

/-- Original channel data, in the original stage order. No new numerical
oracle or alternative statistical input is introduced. -/
def inputSchedule (input : StatisticalInput I) : ExperimentSchedule I.Tool :=
  List.ofFn (fun stage : I.Stage => (I.eligible stage, input.experiment stage))

theorem weights_inputSchedule (input : StatisticalInput I) :
    weights (inputSchedule input) = input.weightedSchedule := by
  simp only [weights, inputSchedule, List.map_ofFn, StatisticalInput.weightedSchedule, Function.comp_def]

theorem compatibility_inputSchedule (input : StatisticalInput I) :
    compatibility (inputSchedule input) = I.compatibility := by
  rw [← weights_eligibility, weights_inputSchedule, input.weightedSchedule_eligibility]

def inputExpression (input : StatisticalInput I) (remaining : Finset I.Tool) : Expr :=
  leadingExpression (inputSchedule input) remaining

/-- Exact symbolic leading coefficient for the same original input,
including the zero expression at infinite rank. -/
theorem inputExpression_eval (input : StatisticalInput I) (remaining : Finset I.Tool) :
    (inputExpression input remaining).eval = input.orderedCoefficient remaining := by
  rw [inputExpression, leadingExpression_eval, weights_inputSchedule]
  rfl

def inputHeads (input : StatisticalInput I) (remaining : Finset I.Tool) : List (ℕ × BinaryExperiment) :=
  if genericRank I.compatibility remaining = ⊤ then []
  else heads (inputSchedule input) remaining (genericRank I.compatibility remaining) 0

theorem inputHeads_length_le (input : StatisticalInput I) (remaining : Finset I.Tool) :
    (inputHeads input remaining).length ≤ I.stageCount := by
  unfold inputHeads
  split
  · exact Nat.zero_le _
  · have h := heads_length_le (inputSchedule input) remaining (genericRank I.compatibility remaining) 0
    simpa only [inputSchedule, List.length_ofFn, Instance.stageCount] using h

theorem inputExpression_eq_head_sum (input : StatisticalInput I) (remaining : Finset I.Tool) :
    inputExpression input remaining =
      sumExpr ((inputHeads input remaining).map (fun head => localCoefficientExpr head.2)) := by
  simp only [inputExpression, leadingExpression, compatibility_inputSchedule, inputHeads]
  split
  · rfl
  · rfl

def Expr.nodes : Expr → ℕ
  | .rational _ => 1
  | .add left right | .multiply left right | .divide left right => 1 + left.nodes + right.nodes
  | .log argument => 1 + argument.nodes

theorem sumExpr_nodes (expressions : List Expr) :
    (sumExpr expressions).nodes = (expressions.map (fun expression => expression.nodes + 1)).sum + 1 := by
  induction expressions with
  | nil => rfl
  | cons head later ih =>
    simp only [sumExpr, Expr.nodes, List.map_cons, List.sum_cons, ih]
    omega

theorem divergenceExpr_nodes (E : BinaryExperiment) (truth : Bool) :
    (divergenceExpr E truth).nodes = 7 * E.alphabetSize + 1 := by
  rw [divergenceExpr, sumExpr_nodes, List.map_ofFn]
  change (List.ofFn (fun _ : Fin E.alphabetSize => 7)).sum + 1 = _
  simp only [List.ofFn_const, List.sum_replicate, Nat.nsmul_eq_mul]
  omega

theorem localCoefficientExpr_nodes (E : BinaryExperiment) :
    (localCoefficientExpr E).nodes = 14 * E.alphabetSize + 9 := by
  simp only [localCoefficientExpr, Expr.nodes, divergenceExpr_nodes]
  omega

/-- A linear-size symbolic expression: each selected stage contributes
its original finite channel formula once; no execution tree is expanded. -/
theorem heads_expression_nodes_le {Tool : Type*} [DecidableEq Tool]
    (stages : ExperimentSchedule Tool) (remaining : Finset Tool) (target : ℕ∞) (offset : ℕ) :
    (sumExpr ((heads stages remaining target offset).map (fun head => localCoefficientExpr head.2))).nodes ≤
      (stages.map (fun stage => 14 * stage.2.alphabetSize + 10)).sum + 1 := by
  induction stages generalizing offset with
  | nil => rfl
  | cons stage later ih =>
    rcases stage with ⟨eligible, E⟩
    simp only [heads, List.map_cons, List.sum_cons]
    split
    · simp only [List.map_cons, sumExpr, Expr.nodes, localCoefficientExpr_nodes]
      have h := ih (offset + 1)
      omega
    · have h := ih (offset + 1)
      omega

theorem inputExpression_nodes_le (input : StatisticalInput I) (remaining : Finset I.Tool) :
    (inputExpression input remaining).nodes ≤
      (List.ofFn (fun stage : I.Stage => 14 * (input.experiment stage).alphabetSize + 10)).sum + 1 := by
  unfold inputExpression leadingExpression
  split
  · change 1 ≤ _ + 1
    omega
  · exact (heads_expression_nodes_le (inputSchedule input) remaining _ 0).trans_eq (by
      simp only [inputSchedule, List.map_ofFn, Function.comp_def])

end PaperProofs.Common.SymbolicPrice
