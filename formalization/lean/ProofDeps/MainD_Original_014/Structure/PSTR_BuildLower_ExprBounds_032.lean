module

public import Structure.PSTR_BuildLower_DynamicWord_026
public import PaperProofs.Structure.PA17_WordBounds_023

/-! Exact Nat-to-Word Expr compatibility uses values of the expression tree,
not a global no-wrap assertion for backend shifts or actual packed bodies.
The fixed fullBuild syntax has a small cubic arithmetic envelope. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ExprBounds
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PA17UniformGenerator035b PA17ProgramTemplates041

def coefficient : Expr → Nat
  | .constant value => value + 1
  | .cell _ | .input _ => 1
  | .binary .multiply left right => coefficient left * coefficient right
  | .binary _ left right => coefficient left + coefficient right

def degree : Expr → Nat
  | .constant _ => 0
  | .cell _ | .input _ => 1
  | .binary .multiply left right => degree left + degree right
  | .binary _ left right => max (degree left) (degree right)

def arithmetic : Expr → Bool
  | .constant _ | .cell _ | .input _ => true
  | .binary operation left right =>
    (match operation with | .add | .subtract | .minimum | .multiply => true | _ => false) &&
      arithmetic left && arithmetic right

theorem coefficient_pos (expr : Expr) : 0 < coefficient expr := by
  induction expr with
  | constant value => simp [coefficient]
  | cell address => change 0 < 1; decide
  | input address => change 0 < 1; decide
  | binary operation left right ihl ihr =>
    cases operation <;> simp only [coefficient] <;> first | exact Nat.mul_pos ihl ihr | omega

theorem eval_le (expr : Expr) (rom : PhysicalROM) (environment : Nat → Nat) (B : Nat)
    (hB : 1 ≤ B) (ha : arithmetic expr = true)
    (hc : ∀ address, environment address ≤ B)
    (hd : ∀ address, rom.semantic.read .input address ≤ B) :
    expr.eval rom environment ≤ coefficient expr * B ^ degree expr := by
  induction expr with
  | constant value => simp [Expr.eval, coefficient, degree]
  | cell address => simpa only [Expr.eval, coefficient, degree, pow_one, Nat.one_mul] using hc address
  | input address => simpa only [Expr.eval, coefficient, degree, pow_one, Nat.one_mul] using hd address
  | binary operation left right ihl ihr =>
    have hleft : arithmetic left = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ha).1).2
    have hright : arithmetic right = true := (Bool.and_eq_true_iff.mp ha).2
    have hl := ihl hleft
    have hr := ihr hright
    have hpL := Nat.pow_le_pow_right hB (Nat.le_max_left (degree left) (degree right))
    have hpR := Nat.pow_le_pow_right hB (Nat.le_max_right (degree left) (degree right))
    have hls := hl.trans (Nat.mul_le_mul_left (coefficient left) hpL)
    have hrs := hr.trans (Nat.mul_le_mul_left (coefficient right) hpR)
    cases operation with
    | add =>
      simpa only [Expr.eval, Binary.eval, coefficient, degree, Nat.add_mul] using Nat.add_le_add hls hrs
    | subtract =>
      exact (Nat.sub_le _ _).trans (hls.trans (by simp only [coefficient, degree, Nat.add_mul]; omega))
    | minimum =>
      exact (min_le_left _ _).trans (hls.trans (by simp only [coefficient, degree, Nat.add_mul]; omega))
    | multiply =>
      have hh := Nat.mul_le_mul hl hr
      simpa only [Expr.eval, Binary.eval, coefficient, degree, pow_add, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm] using hh
    | divide | bitAnd | bitOr | shiftLeft | shiftRight => simp [arithmetic] at ha

def certified (expr : Expr) : Bool := arithmetic expr && decide (coefficient expr ≤ 65536 ∧ degree expr ≤ 3)

def programCertified : Program → Bool
  | .code ops => ops.all (fun op => match op with | .constant _ expr => certified expr | .literal _ => true)
  | .append left right => programCertified left && programCertified right
  | .repeat _ bound body => certified bound && programCertified body

theorem fullBuild_certified : programCertified fullBuild = true := by decide

theorem binaryWordEval_ofNat (bits : Nat) (operation : Binary) (left right : Nat)
    (hl : Fits bits left) (hr : Fits bits right) :
    binaryWordEval operation (BitVec.ofNat bits left) (BitVec.ofNat bits right) =
      BitVec.ofNat bits (operation.eval left right) := by
  cases operation <;>
    simp [binaryWordEval, Binary.eval, packingArithmetic, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr, BitVec.ofNat_add_ofNat, min_def, apply_ite]
  split_ifs <;> intro h <;> omega

def nodesFit (bits : Nat) (rom : PhysicalROM) (environment : Nat → Nat) : Expr → Prop
  | .binary operation left right => Fits bits ((.binary operation left right : Expr).eval rom environment) ∧
      nodesFit bits rom environment left ∧ nodesFit bits rom environment right
  | expr => Fits bits (expr.eval rom environment)

theorem nodesFit_value {bits : Nat} {rom : PhysicalROM} {environment : Nat → Nat} {expr : Expr}
    (hf : nodesFit bits rom environment expr) : Fits bits (expr.eval rom environment) := by
  cases expr <;> first | exact hf | exact hf.1

theorem children_limits (operation : Binary) (left right : Expr) :
    coefficient left ≤ coefficient (.binary operation left right) ∧
    coefficient right ≤ coefficient (.binary operation left right) ∧
    degree left ≤ degree (.binary operation left right) ∧
    degree right ≤ degree (.binary operation left right) := by
  have hl := coefficient_pos left
  have hr := coefficient_pos right
  have hdl := Nat.le_max_left (degree left) (degree right)
  have hdr := Nat.le_max_right (degree left) (degree right)
  cases operation <;> simp only [coefficient, degree] <;> repeat' constructor
  all_goals first | omega | nlinarith

theorem nodesFit_of_envelope (bits : Nat) (expr : Expr) (rom : PhysicalROM) (environment : Nat → Nat) (B : Nat)
    (hB : 1 ≤ B) (ha : arithmetic expr = true) (hco : coefficient expr ≤ 65536) (hde : degree expr ≤ 3)
    (hc : ∀ address, environment address ≤ B)
    (hd : ∀ address, rom.semantic.read .input address ≤ B)
    (hfit : Fits bits (65536 * B ^ 3)) : nodesFit bits rom environment expr := by
  have bound (sub : Expr) (har : arithmetic sub = true) (hcs : coefficient sub ≤ 65536) (hds : degree sub ≤ 3) :
      Fits bits (sub.eval rom environment) := by
    have hh := eval_le sub rom environment B hB har hc hd
    exact (hh.trans (Nat.mul_le_mul hcs (Nat.pow_le_pow_right hB hds))).trans_lt hfit
  induction expr with
  | constant value => exact bound _ ha hco hde
  | cell address => exact bound _ ha hco hde
  | input address => exact bound _ ha hco hde
  | binary operation left right ihl ihr =>
    have hleft : arithmetic left = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ha).1).2
    have hright : arithmetic right = true := (Bool.and_eq_true_iff.mp ha).2
    have limits := children_limits operation left right
    refine ⟨bound _ ha hco hde, ihl hleft (limits.1.trans hco) (limits.2.2.1.trans hde),
      ihr hright (limits.2.1.trans hco) (limits.2.2.2.trans hde)⟩

theorem wordEval_exact (bits : Nat) (expr : Expr) (rom : PhysicalROM) (environment : Nat → Nat)
    (hf : nodesFit bits rom environment expr)
    (hi : ∀ address < expressionInputLimit expr, Fits bits address) :
    exprWordEval rom (fun address => BitVec.ofNat bits (environment address)) expr =
      BitVec.ofNat bits (expr.eval rom environment) := by
  induction expr with
  | constant value => rfl
  | cell address => rfl
  | input address =>
    have ha : Fits bits address := hi address (by simp [expressionInputLimit])
    simp only [exprWordEval, Expr.eval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
    rfl
  | binary operation left right ihl ihr =>
    have hl := ihl hf.2.1 (fun address ha => hi address (lt_of_lt_of_le ha (Nat.le_max_left _ _)))
    have hr := ihr hf.2.2 (fun address ha => hi address (lt_of_lt_of_le ha (Nat.le_max_right _ _)))
    simp only [exprWordEval, Expr.eval, hl, hr]
    exact binaryWordEval_ofNat bits operation _ _ (nodesFit_value hf.2.1) (nodesFit_value hf.2.2)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ExprBounds
