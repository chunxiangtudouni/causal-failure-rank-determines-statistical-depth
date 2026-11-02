module

public import B23_4_RatWordPrep_SeqCmp_WordCountToResources_157

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

/-- A proof-side syntax for fixed nonnegative polynomial budgets. No
runtime source, memory, or branch is selected by this data. -/
inductive PolynomialBudget where
  | constant (value : Nat)
  | input
  | add (left right : PolynomialBudget)
  | mul (left right : PolynomialBudget)
  | power (base : PolynomialBudget) (exponent : Nat)

namespace PolynomialBudget

def eval : PolynomialBudget → Nat → Nat
  | .constant value,_ => value
  | .input,bound => bound
  | .add left right,bound => left.eval bound+right.eval bound
  | .mul left right,bound => left.eval bound*right.eval bound
  | .power base exponent,bound => (base.eval bound)^exponent

def coefficient : PolynomialBudget → Nat
  | .constant value => value
  | .input => 1
  | .add left right => left.coefficient+right.coefficient
  | .mul left right => left.coefficient*right.coefficient
  | .power base exponent => base.coefficient^exponent

def degree : PolynomialBudget → Nat
  | .constant _ => 0
  | .input => 1
  | .add left right => max left.degree right.degree
  | .mul left right => left.degree+right.degree
  | .power base exponent => base.degree*exponent

theorem eval_bound (budget : PolynomialBudget) (bound : Nat) :
    budget.eval bound≤budget.coefficient*(bound+1)^budget.degree := by
  induction budget with
  | constant value => simp [eval,coefficient,degree]
  | input => simpa only [eval,coefficient,degree,pow_one,one_mul] using Nat.le_succ bound
  | add left right hl hr =>
    have a := Nat.pow_le_pow_right (Nat.succ_pos bound) (Nat.le_max_left left.degree right.degree)
    have b := Nat.pow_le_pow_right (Nat.succ_pos bound) (Nat.le_max_right left.degree right.degree)
    have al := hl.trans (Nat.mul_le_mul_left left.coefficient a)
    have br := hr.trans (Nat.mul_le_mul_left right.coefficient b)
    exact (Nat.add_le_add al br).trans_eq (Nat.add_mul left.coefficient right.coefficient
      ((bound+1)^max left.degree right.degree)).symm
  | mul left right hl hr =>
    exact (Nat.mul_le_mul hl hr).trans_eq (by simp only [coefficient,degree,pow_add]; ring)
  | power base exponent hb =>
    exact (Nat.pow_le_pow_left hb exponent).trans_eq (by simp only [coefficient,degree,mul_pow,pow_mul])

end PolynomialBudget

end B23_4_RatWordPrep.WordFinish.Resources
