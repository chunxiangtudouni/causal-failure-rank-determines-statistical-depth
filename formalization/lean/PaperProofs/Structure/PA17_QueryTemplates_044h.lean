module
public import PaperProofs.Structure.PA17_QueryTemplates_044g
public import PaperProofs.Structure.PA17_UniformGenerator_035j
import Mathlib.Tactic.Ring

/-! Polynomial envelopes bound every subexpression of the actual query AST,
not only the eventual emitted immediate. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044h
open IndexedRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035j

def Good : Expr → Prop
  | .constant _ | .cell _ | .input _ => True
  | .binary op left right =>
    (op = .add ∨ op = .subtract ∨ op = .minimum ∨ op = .multiply ∨ op = .divide) ∧ Good left ∧ Good right

def degree : Expr → Nat
  | .constant _ => 0
  | .cell _ | .input _ => 1
  | .binary .multiply left right => degree left + degree right
  | .binary _ left right => max (degree left) (degree right)

def coefficient : Expr → Nat
  | .constant value => value + 1
  | .cell _ | .input _ => 1
  | .binary .multiply left right => coefficient left * coefficient right
  | .binary _ left right => coefficient left + coefficient right

theorem coefficient_pos (expression : Expr) : 0 < coefficient expression := by
  induction expression with
  | constant value => simp [coefficient]
  | cell address => simp [coefficient]
  | input address => simp [coefficient]
  | binary operation left right ihl ihr =>
    cases operation <;> simp only [coefficient]
    all_goals first | exact Nat.mul_pos ihl ihr | omega

theorem child_bounds (operation : Binary) (left right : Expr) :
    coefficient left ≤ coefficient (.binary operation left right) ∧
    coefficient right ≤ coefficient (.binary operation left right) ∧
    degree left ≤ degree (.binary operation left right) ∧ degree right ≤ degree (.binary operation left right) := by
  have hl := coefficient_pos left
  have hr := coefficient_pos right
  cases operation <;> simp only [coefficient, degree]
  all_goals exact ⟨by nlinarith, by nlinarith, by omega, by omega⟩

theorem budget_mono (u c d largerC largerD : Nat) (hu : 1 ≤ u) (hc : c ≤ largerC) (hd : d ≤ largerD) :
    c * u ^ d ≤ largerC * u ^ largerD := Nat.mul_le_mul hc (pow_le_pow_right' hu hd)

theorem value_le (expression : Expr) (rom : PhysicalROM) (env : Nat → Nat) (u : Nat) (hu : 1 ≤ u)
    (scope : Finset Nat) (hs : expression.cells ⊆ scope) (henv : ∀ address ∈ scope, env address ≤ u)
    (hi : expression.InputsBelow 3) (hinput : ∀ address < 3, rom.semantic.read .input address ≤ u)
    (hg : Good expression) : expression.eval rom env ≤ coefficient expression * u ^ degree expression := by
  induction expression with
  | constant value => simp [Expr.eval, coefficient, degree]
  | cell address =>
    exact (henv address (hs (by simp [Expr.cells]))).trans (by simp [coefficient, degree])
  | input address => exact (hinput address hi).trans (by simp [coefficient, degree])
  | binary operation left right ihl ihr =>
    have hl := ihl (fun address ha => hs (Finset.mem_union_left _ ha)) hi.1 hg.2.1
    have hr := ihr (fun address ha => hs (Finset.mem_union_right _ ha)) hi.2 hg.2.2
    have hl' : left.eval rom env ≤ coefficient left * u ^ max (degree left) (degree right) :=
      hl.trans (budget_mono _ _ _ _ _ hu le_rfl (Nat.le_max_left _ _))
    have hr' : right.eval rom env ≤ coefficient right * u ^ max (degree left) (degree right) :=
      hr.trans (budget_mono _ _ _ _ _ hu le_rfl (Nat.le_max_right _ _))
    rcases hg.1 with rfl | rfl | rfl | rfl | rfl
    · change left.eval rom env + right.eval rom env ≤ (coefficient left + coefficient right) * u ^ max (degree left) (degree right)
      calc
        _ ≤ coefficient left * u ^ max (degree left) (degree right) + coefficient right * u ^ max (degree left) (degree right) := Nat.add_le_add hl' hr'
        _ = _ := by ring
    · change left.eval rom env - right.eval rom env ≤ (coefficient left + coefficient right) * u ^ max (degree left) (degree right)
      exact (Nat.sub_le _ _).trans (hl'.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
    · change min (left.eval rom env) (right.eval rom env) ≤ (coefficient left + coefficient right) * u ^ max (degree left) (degree right)
      exact (Nat.min_le_left _ _).trans (hl'.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
    · change left.eval rom env * right.eval rom env ≤ (coefficient left * coefficient right) * u ^ (degree left + degree right)
      calc
        _ ≤ (coefficient left * u ^ degree left) * (coefficient right * u ^ degree right) := Nat.mul_le_mul hl hr
        _ = _ := by rw [pow_add]; ring
    · change left.eval rom env / right.eval rom env ≤ (coefficient left + coefficient right) * u ^ max (degree left) (degree right)
      exact (Nat.div_le_self _ _).trans (hl'.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))

theorem expression_checked (expression : Expr) (rom : PhysicalROM) (env : Nat → Nat)
    (u B heapWords : Nat) (hu : 1 ≤ u) (hB : 64 ≤ B) (hheap : 64 ≤ heapWords)
    (scope : Finset Nat) (hs : expression.cells ⊆ scope) (henv : ∀ address ∈ scope, env address ≤ u)
    (ha : expression.Below 64) (hi : expression.InputsBelow 3) (hinputlen : 3 ≤ rom.input.length)
    (hinput : ∀ address < 3, rom.semantic.read .input address ≤ u) (hg : Good expression)
    (hb : coefficient expression * u ^ degree expression ≤ B) : ExprChecked rom env B heapWords expression := by
  induction expression with
  | constant value =>
    change value ≤ B
    simp only [coefficient, degree, pow_zero, Nat.mul_one] at hb
    omega
  | cell address =>
    change address < heapWords ∧ address ≤ B ∧ env address ≤ B
    change address < 64 at ha
    refine ⟨ha.trans_le hheap, by omega, ?_⟩
    exact (value_le (.cell address) rom env u hu scope hs henv hi hinput hg).trans hb
  | input address =>
    change address < 3 at hi
    exact ⟨hi.trans_le hinputlen, by omega,
      (value_le (.input address) rom env u hu scope hs henv hi hinput hg).trans hb⟩
  | binary operation left right ihl ihr =>
    have hchildren := child_bounds operation left right
    refine ⟨ihl (fun address hm => hs (Finset.mem_union_left _ hm)) ha.1 hi.1 hg.2.1
      ((budget_mono _ _ _ _ _ hu hchildren.1 hchildren.2.2.1).trans hb),
      ihr (fun address hm => hs (Finset.mem_union_right _ hm)) ha.2 hi.2 hg.2.2
      ((budget_mono _ _ _ _ _ hu hchildren.2.1 hchildren.2.2.2).trans hb), ?_⟩
    exact (value_le (.binary operation left right) rom env u hu scope hs henv hi hinput hg).trans hb

end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044h
