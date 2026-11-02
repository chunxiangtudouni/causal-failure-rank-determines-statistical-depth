module
public import Common.PSTR_SYM_InputBits_003

/-! Paper-only exact symbolic construction. The high-level model has finite
constructor nodes and linked input records. A node emission and a record/link
navigation each cost one; copying a supplied rational bit costs one read and
one write. Rational values below denote their supplied sign/numerator/denominator
bitstrings. They are never numerically evaluated by the construction. In
particular 1-prior is syntax, not an extra rational arithmetic primitive.

The instrumented recursion is the algorithm, not a cost-oracle premise.
`copyBits` accounts for every read/write; constructor routines account for
every emitted node; row recursion accounts for input-record navigation.
No Bool-machine implementation, parser or fixed output serialization is claimed.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.Symbolic
open PaperProofs.Common.SymbolicPrice PaperProofs.Statistics
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.RationalControllerComputation.PSTRTMLength004
open PSTRSymbolicBits

/-- A view of ONE rational leaf already present in the original input.
The representation equation is a proof field, not additional input data. -/
structure GivenRat where
  value : ℚ
  bits : List Bool
  represents : bits = encodeDatum (.rational value)

def given (value : ℚ) : GivenRat := ⟨value, encodeDatum (.rational value), rfl⟩

def copyBits : List Bool → List Bool × Nat
  | [] => ([], 0)
  | bit :: later =>
      let copied := copyBits later
      (bit :: copied.1, 2 + copied.2)

theorem copyBits_exact (bits : List Bool) :
    (copyBits bits).1 = bits ∧ (copyBits bits).2 = 2 * bits.length := by
  induction bits with
  | nil => exact ⟨rfl, rfl⟩
  | cons bit later ih =>
    simp only [copyBits, List.length_cons, ih.1, ih.2]
    constructor
    · exact True.intro
    · omega

/-- Payload bits of all rational-leaf occurrences. Fixed constants count too. -/
def leafBits : Expr → Nat
  | .rational value => ratBits value
  | .add left right | .multiply left right | .divide left right => leafBits left + leafBits right
  | .log argument => leafBits argument

structure Built where
  expression : Expr
  emitted : Nat
  copied : Nat
  navigated : Nat
  emitted_exact : emitted = expression.nodes
  copied_exact : copied = 2 * leafBits expression

def Built.work (output : Built) : Nat := output.emitted + output.copied + output.navigated

theorem Built.output_le_work (output : Built) :
    output.expression.nodes + leafBits output.expression ≤ output.work := by
  rw [Built.work, output.emitted_exact, output.copied_exact]
  omega

def copyRat (input : GivenRat) : Built :=
  { expression := .rational input.value
    emitted := 1
    copied := (copyBits input.bits).2
    navigated := 0
    emitted_exact := rfl
    copied_exact := by
      rw [(copyBits_exact input.bits).2, input.represents]
      simp only [leafBits, ratBits, encodeDatum_length] }

def constant (value : ℚ) : Built := copyRat (given value)

def add (left right : Built) : Built :=
  { expression := .add left.expression right.expression
    emitted := 1 + left.emitted + right.emitted
    copied := left.copied + right.copied
    navigated := left.navigated + right.navigated
    emitted_exact := by simp only [Expr.nodes, left.emitted_exact, right.emitted_exact]
    copied_exact := by simp only [leafBits, left.copied_exact, right.copied_exact]; omega }

def multiply (left right : Built) : Built :=
  { expression := .multiply left.expression right.expression
    emitted := 1 + left.emitted + right.emitted
    copied := left.copied + right.copied
    navigated := left.navigated + right.navigated
    emitted_exact := by simp only [Expr.nodes, left.emitted_exact, right.emitted_exact]
    copied_exact := by simp only [leafBits, left.copied_exact, right.copied_exact]; omega }

def divide (left right : Built) : Built :=
  { expression := .divide left.expression right.expression
    emitted := 1 + left.emitted + right.emitted
    copied := left.copied + right.copied
    navigated := left.navigated + right.navigated
    emitted_exact := by simp only [Expr.nodes, left.emitted_exact, right.emitted_exact]
    copied_exact := by simp only [leafBits, left.copied_exact, right.copied_exact]; omega }

def log (argument : Built) : Built :=
  { expression := .log argument.expression
    emitted := 1 + argument.emitted
    copied := argument.copied
    navigated := argument.navigated
    emitted_exact := by simp only [Expr.nodes, argument.emitted_exact]
    copied_exact := by simp only [leafBits, argument.copied_exact] }

def navigate (steps : Nat) (output : Built) : Built :=
  { output with navigated := steps + output.navigated }

theorem copyRat_copied (input : GivenRat) : (copyRat input).copied = 2 * ratBits input.value :=
  (copyRat input).copied_exact

theorem given_bits (value : ℚ) : (given value).bits.length = ratBits value := by
  simp only [given, ratBits, encodeDatum_length]

theorem constant_zero :
    (constant 0).emitted = 1 ∧ (constant 0).copied = 16 ∧ (constant 0).navigated = 0 := by
  simp only [constant, copyRat, given, (copyBits_exact _).2]
  norm_num [encodeDatum_length, datumBits, natBits]

theorem fixed_rat_bits (value : ℚ) (h : value = 0 ∨ value = 1 ∨ value = -1) :
    ratBits value = 8 := by
  rcases h with rfl | rfl | rfl <;> norm_num [ratBits, datumBits, natBits]

abbrev Row := GivenRat × GivenRat

def rowLeft (truth : Bool) (row : Row) : GivenRat := if truth then row.2 else row.1
def rowRight (truth : Bool) (row : Row) : GivenRat := if truth then row.1 else row.2

def term (truth : Bool) (row : Row) : Built :=
  multiply (copyRat (rowLeft truth row))
    (log (divide (copyRat (rowLeft truth row)) (copyRat (rowRight truth row))))

/-- Two channel-row descriptors are supplied in original symbol order.
Four navigations cover the row link, pair and two rational-leaf descriptors. -/
def divergence : List Row → Bool → Built
  | [], _ => navigate 1 (constant 0)
  | row :: later, truth => navigate 4 (add (term truth row) (divergence later truth))

def rows (E : BinaryExperiment) : List Row :=
  List.ofFn (fun y : Fin E.alphabetSize => (given (E.channel false y), given (E.channel true y)))

theorem divergence_expression (items : List Row) (truth : Bool) :
    (divergence items truth).expression = sumExpr (items.map (fun row => (term truth row).expression)) := by
  induction items with
  | nil => rfl
  | cons row later ih =>
    simp only [divergence, navigate, add, sumExpr, List.map_cons, ih]

theorem divergence_original (E : BinaryExperiment) (truth : Bool) :
    (divergence (rows E) truth).expression = divergenceExpr E truth := by
  rw [divergence_expression]
  cases truth <;>
    simp only [rows, List.map_ofFn, term, multiply, log, divide, copyRat,
      rowLeft, rowRight, Bool.false_eq_true, ite_false, ite_true, given,
      divergenceExpr, Bool.not_false, Bool.not_true, Function.comp_def]

theorem divergence_emitted (items : List Row) (truth : Bool) :
    (divergence items truth).emitted = 7 * items.length + 1 := by
  induction items with
  | nil => rfl
  | cons row later ih =>
    simp only [divergence, navigate, add, term, multiply, log, divide, copyRat,
      List.length_cons, ih]
    omega

theorem divergence_navigation (items : List Row) (truth : Bool) :
    (divergence items truth).navigated = 4 * items.length + 1 := by
  induction items with
  | nil => rfl
  | cons row later ih =>
    simp only [divergence, navigate, add, term, multiply, log, divide, copyRat,
      List.length_cons, ih]
    omega

def rowBits (items : List Row) (truth : Bool) : Nat :=
  (items.map (fun row => ratBits (rowLeft truth row).value)).sum

theorem divergence_copied (items : List Row) (truth : Bool) :
    (divergence items truth).copied = 16 + 4 * rowBits items truth + 2 * rowBits items (!truth) := by
  induction items with
  | nil =>
    change (constant 0).copied = 16 + 4 * 0 + 2 * 0
    exact constant_zero.2.1
  | cons row later ih =>
    have right : rowRight truth row = rowLeft (!truth) row := by cases truth <;> rfl
    simp only [divergence, navigate, add, term, multiply, log, divide, copyRat_copied,
      rowBits, List.map_cons, List.sum_cons] at ih ⊢
    rw [right]
    omega

theorem rows_bits (E : BinaryExperiment) :
    rowBits (rows E) false + rowBits (rows E) true = channelMass E := by
  simp only [rowBits, rows, rowLeft, Bool.false_eq_true, ite_false, ite_true,
    given, channelMass, List.ofFn_eq_map, List.map_map, Function.comp_def]

/-- Three header-field navigations; every channel pass is separately charged. -/
def stageBuild (E : BinaryExperiment) : Built :=
  navigate 3 (multiply (copyRat (given E.observationFee))
    (add (divide (add (constant 1) (multiply (constant (-1)) (copyRat (given E.priorOne))))
        (divergence (rows E) false))
      (divide (copyRat (given E.priorOne)) (divergence (rows E) true))))

theorem prior_complement_eval (E : BinaryExperiment) :
    (add (constant 1) (multiply (constant (-1)) (copyRat (given E.priorOne)))).expression.eval =
      (E.prior false : ℝ) := by
  simp only [add, multiply, constant, copyRat, given, Expr.eval, BinaryExperiment.prior,
    Bool.false_eq_true, ite_false, Rat.cast_sub, Rat.cast_one, Rat.cast_neg]
  ring

theorem local_eval (E : BinaryExperiment) :
    (stageBuild E).expression.eval = E.coefficient := by
  rw [← localCoefficientExpr_eval E]
  simp only [stageBuild, navigate, multiply, add, divide, copyRat, given, Expr.eval,
    divergence_original, localCoefficientExpr, constant, BinaryExperiment.prior,
    Bool.false_eq_true, ite_false, ite_true, Rat.cast_one, Rat.cast_neg, Rat.cast_sub]
  ring

theorem local_emitted (E : BinaryExperiment) : (stageBuild E).emitted = 14 * E.alphabetSize + 13 := by
  simp only [stageBuild, navigate, multiply, add, divide, copyRat, constant,
    divergence_emitted, rows, List.length_ofFn]
  omega

theorem local_navigation (E : BinaryExperiment) : (stageBuild E).navigated = 8 * E.alphabetSize + 5 := by
  simp only [stageBuild, navigate, multiply, add, divide, copyRat, constant,
    divergence_navigation, rows, List.length_ofFn]
  omega

theorem local_copied (E : BinaryExperiment) :
    (stageBuild E).copied = 64 + 2 * ratBits E.observationFee + 4 * ratBits E.priorOne + 6 * channelMass E := by
  have one := fixed_rat_bits 1 (Or.inr (Or.inl rfl))
  have negone := fixed_rat_bits (-1) (Or.inr (Or.inr rfl))
  have rb := rows_bits E
  simp only [stageBuild, navigate, multiply, add, divide, constant, copyRat_copied,
    given, divergence_copied, Bool.not_false, Bool.not_true, one, negone]
  omega

/-- A bound on the ACTUAL counted construction, including bit copying and
all row navigation; no evaluation of rational ratios or logarithms occurs. -/
theorem local_work_le (E : BinaryExperiment) :
    (stageBuild E).work ≤ 32 * datumMass (rawExperiment E) := by
  have channels := channelMass_ge E
  have prior := ratBits_ge_eight E.priorOne
  have fee := ratBits_ge_eight E.observationFee
  have header : 4 ≤ datumBits (.natural E.alphabetSize) := by
    simp only [datumBits, natBits]
    omega
  rw [Built.work, local_emitted, local_copied, local_navigation, rawExperiment_mass]
  omega

end RootPaper.Symbolic
