module

public import RootPaper_Prep_Algorithm001
public import RootB234_ECost_Widths001
public import RootB23_WordOddsBits_Input_002

/-! A preparation-specific arithmetic cost schedule. These lists are erased
cost annotations of the high-level recursion, not a runtime output or a VM.
Each entry names the actual operands of one arithmetic/copy/branch operation.
In particular a loop test is charged for producing its powers and thresholds.
No supplied exponent, quota, cost certificate, or numerical cap is used as fuel. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open scoped BigOperators
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.PSTRWordBool

namespace RootPaper.Prep

abbrev field := RatInput.Encoder.fieldSize

inductive Arithmetic where
  | add | sub | mul | div | le
  deriving DecidableEq

/-- Only the fixed operations appearing in preparation. There is no program
counter, register language, evaluator, external arithmetic oracle, or ISA. -/
inductive Operation where
  | rational (kind : Arithmetic) (x y : Rat)
  | natural (n : Nat)
  | branch

def Operation.width : Operation → Nat
  | .rational _ x y => field x+field y+1
  | .natural n => field (n : Rat)+1
  | .branch => 1

/-- Frozen binary rational implementations have degree four with these
input-independent coefficients. The extra factors cover encoding the two
canonical operands, copying their sign/magnitude, and a comparison's sign test. -/
def primitiveRate : Nat :=
  64^4*(RatAddSub.addSubCoefficient+RatMulDiv.mulCoefficient+RatMulDiv.divCoefficient+1)

theorem primitiveRate_pos : 0 < primitiveRate := by
  unfold primitiveRate
  exact Nat.mul_pos (by decide) (by omega)

def Operation.bitCost (op : Operation) : Nat := primitiveRate*(op.width+1)^4

def bitCost (ops : List Operation) : Nat := (ops.map Operation.bitCost).sum

def Bounded (ops : List Operation) (count width : Nat) : Prop :=
  ops.length ≤ count ∧ ∀ op ∈ ops, op.width ≤ width

theorem bounded_nil (count width : Nat) : Bounded [] count width := by simp [Bounded]

theorem bounded_mono {ops : List Operation} {count width count' width' : Nat}
    (h : Bounded ops count width) (hc : count ≤ count') (hw : width ≤ width') :
    Bounded ops count' width' := ⟨h.1.trans hc, fun op member => (h.2 op member).trans hw⟩

theorem bounded_append {xs ys : List Operation} {cx cy w : Nat}
    (hx : Bounded xs cx w) (hy : Bounded ys cy w) : Bounded (xs++ys) (cx+cy) w := by
  constructor
  · simpa only [List.length_append] using Nat.add_le_add hx.1 hy.1
  · intro op member
    rcases List.mem_append.mp member with member | member
    · exact hx.2 op member
    · exact hy.2 op member

theorem bounded_flatMap {α : Type*} (xs : List α) (f : α → List Operation) (c w : Nat)
    (each : ∀ x ∈ xs, Bounded (f x) c w) : Bounded (xs.flatMap f) (xs.length*c) w := by
  induction xs with
  | nil => simp [Bounded]
  | cons x xs ih =>
    simpa only [List.flatMap_cons, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
      bounded_append (each x List.mem_cons_self)
        (ih (fun y member => each y (List.mem_cons_of_mem x member)))

theorem bounded_bitCost {ops : List Operation} {count width : Nat} (h : Bounded ops count width) :
    bitCost ops ≤ count*primitiveRate*(width+1)^4 := by
  have summed : bitCost ops ≤ ops.length*(primitiveRate*(width+1)^4) := by
    unfold bitCost
    have bound := List.sum_le_length_nsmul (ops.map Operation.bitCost) (primitiveRate*(width+1)^4) (by
      intro cost member
      obtain ⟨op, present, rfl⟩ := List.mem_map.mp member
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (h.2 op present) 1) 4))
    simpa only [List.length_map, smul_eq_mul] using bound
  exact summed.trans ((Nat.mul_le_mul_right _ h.1).trans_eq (by ring))

/-- Repeated multiplication, not a unit-cost exponentiation instruction. -/
def powerOps (n : Nat) : List Operation :=
  (List.range n).map (fun k => .rational .mul ((2 : Rat)^k) 2)

def naturalLE (n m : Nat) : List Operation :=
  [.natural n, .natural m, .rational .le (n : Rat) (m : Rat), .branch]

def naturalAdd (n m : Nat) : List Operation :=
  [.natural n, .natural m, .rational .add (n : Rat) (m : Rat), .natural (n+m)]

def ratioTestOps (r : Rat) (n : Nat) : List Operation :=
  powerOps n ++ [.rational .div 1 r, .rational .le r ((2 : Rat)^n),
    .rational .le (1/r) ((2 : Rat)^n), .branch]

def ratioOps (r : Rat) (n : Nat) : List Operation :=
  if ratioTest r n then ratioTestOps r n else
    ratioTestOps r n ++ naturalAdd n 1 ++ ratioOps r (n+1)
termination_by BinaryExperiment.ratioIntegerBound r - n
decreasing_by
  have : n < BinaryExperiment.ratioIntegerBound r := by
    have failed : ¬BinaryExperiment.ratioIntegerBound r ≤ n := by
      intro bounded
      exact (by assumption : ratioTest r n ≠ true) ((ratioTest_iff r n).2 bounded)
    omega
  omega

def exponentTestOps (budget : Rat) (N n : Nat) : List Operation :=
  powerOps (N+1) ++ powerOps n ++ naturalLE 1 n ++
    [.natural N, .rational .mul 6 ((2 : Rat)^(N+1)), .rational .mul 2 (N : Rat),
      .rational .mul (2*(N : Rat)) (6*(2 : Rat)^(N+1)),
      .rational .mul ((2 : Rat)^n) budget,
      .rational .le (2*(N : Rat)*(6*(2 : Rat)^(N+1))) ((2 : Rat)^n*budget), .branch]

def exponentOps (budget : Rat) (positive : 0 < budget) (N n : Nat) : List Operation :=
  if exponentTest budget N n then exponentTestOps budget N n else
    exponentTestOps budget N n ++ naturalAdd n 1 ++ exponentOps budget positive N (n+1)
termination_by BinaryExperiment.quotaExponent budget N - n
decreasing_by
  have : n < BinaryExperiment.quotaExponent budget N := by
    have failed : ¬BinaryExperiment.quotaExponent budget N ≤ n := by
      intro bounded
      exact (by assumption : exponentTest budget N n ≠ true)
        ((exponentTest_iff budget positive N n).2 bounded)
    omega
  omega

def quotaTestOps (e b m : Nat) (d : Rat) (n : Nat) : List Operation :=
  [.natural e, .natural b, .natural m, .natural n,
    .rational .add (e : Rat) (b : Rat), .rational .mul 2 ((e : Rat)+b),
    .rational .mul d (n : Rat), .rational .le (2*((e : Rat)+b)) (d*(n : Rat)),
    .rational .mul (m : Rat) (m : Rat), .rational .mul 8 ((m : Rat)*m),
    .rational .mul (e : Rat) (8*((m : Rat)*m)), .rational .mul d d,
    .rational .mul (d*d) (n : Rat),
    .rational .le ((e : Rat)*(8*((m : Rat)*m))) ((d*d)*(n : Rat)), .branch]

def quotaOps (e b m : Nat) (d : Rat) (positive : 0 < d) (n : Nat) : List Operation :=
  if quotaTest e b m d n then quotaTestOps e b m d n else
    quotaTestOps e b m d n ++ naturalAdd n 1 ++ quotaOps e b m d positive (n+1)
termination_by RootB234.Quota.quota e b m d - n
decreasing_by
  have : n < RootB234.Quota.quota e b m d := by
    have failed : ¬RootB234.Quota.quota e b m d ≤ n := by
      intro bounded
      exact (by assumption : quotaTest e b m d n ≠ true)
        ((quotaTest_iff e b m d positive n).2 bounded)
    omega
  omega

theorem field_one : field (1 : Rat) = 2 := rfl
theorem field_two : field (2 : Rat) = 3 := rfl
theorem field_six : field (6 : Rat) = 4 := rfl
theorem field_eight : field (8 : Rat) = 5 := rfl

theorem field_nat (n : Nat) : field (n : Rat) ≤ n+2 := RootB234.ECost.nat_field n

theorem field_mul (x y : Rat) : field (x*y) ≤ field x+field y := RootB234.ECost.mul_field x y

theorem field_sub (x y : Rat) : field (x-y) ≤ 2*(field x+field y) := RootB234.ECost.sub_field x y

theorem field_power (n : Nat) : field ((2 : Rat)^n) ≤ 2+3*n := by
  have h := RootB234.PrepExponent.QLoop.power_field (1 : Rat) n
  simpa only [one_mul, field_one] using h

theorem field_div (x y : Rat) : field (x/y) ≤ field x+field y := by
  simpa only [field, RootB23.WordOddsBits.ratInput_fieldSize_eq] using
    RootB23.WordOddsBits.div_width_le x y

theorem field_add (x y : Rat) : field (x+y) ≤ 2*(field x+field y) := by
  have h := field_sub x (-y)
  have neg : field (-y) = field y := by
    simp only [field, RootB23.WordOddsBits.ratInput_fieldSize_eq, RootB23.WordOddsBits.width,
      Rat.neg_num, Int.natAbs_neg, Rat.neg_den]
  simpa only [sub_neg_eq_add, neg] using h

theorem powerOps_bounded (n S : Nat) (positive : 1 ≤ S) (bounded : n ≤ S) :
    Bounded (powerOps n) n (12*S) := by
  constructor
  · simp [powerOps]
  · intro op member
    obtain ⟨k, present, rfl⟩ := List.mem_map.mp member
    have kBound : k < n := List.mem_range.mp present
    have width := field_power k
    simp only [Operation.width, field_two]
    omega

theorem naturalLE_bounded (n m S : Nat) (positive : 1 ≤ S)
    (left : field (n : Rat) ≤ S) (right : field (m : Rat) ≤ S) :
    Bounded (naturalLE n m) 4 (4*S) := by
  constructor
  · rfl
  · intro op member
    simp only [naturalLE, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp only [Operation.width] <;> omega

theorem naturalAdd_bounded (n m S : Nat) (positive : 1 ≤ S)
    (left : field (n : Rat) ≤ S) (right : field (m : Rat) ≤ S) :
    Bounded (naturalAdd n m) 4 (8*S) := by
  have added := field_add (n : Rat) (m : Rat)
  have cast : field ((n+m : Nat) : Rat) ≤ 4*S := by
    push_cast
    omega
  constructor
  · rfl
  · intro op member
    simp only [naturalAdd, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp only [Operation.width] <;> omega

theorem ratioTestOps_bounded (r : Rat) (n S : Nat) (positive : 1 ≤ S)
    (rBound : field r ≤ S) (nBound : n ≤ S) :
    Bounded (ratioTestOps r n) (S+4) (32*S) := by
  have pow := field_power n
  have inv := field_div 1 r
  rw [field_one] at inv
  have tail : Bounded [.rational .div 1 r, .rational .le r ((2 : Rat)^n),
      .rational .le (1/r) ((2 : Rat)^n), .branch] 4 (32*S) := by
    constructor
    · rfl
    · intro op member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        simp only [Operation.width, field_one] <;> omega
  exact bounded_mono (bounded_append
    (bounded_mono (powerOps_bounded n S positive nBound) (Nat.le_refl _) (by omega)) tail)
      (by omega) (Nat.le_refl _)

theorem ratioOps_bounded (r : Rat) (n S : Nat) (positive : 1 ≤ S)
    (rBound : field r ≤ S) (limit : BinaryExperiment.ratioIntegerBound r ≤ S)
    (start : n ≤ BinaryExperiment.ratioIntegerBound r) :
    Bounded (ratioOps r n) ((BinaryExperiment.ratioIntegerBound r-n+1)*(S+8)) (64*S) := by
  fun_induction ratioOps r n with
  | case1 n passed =>
    have each := ratioTestOps_bounded r n S positive rBound (start.trans limit)
    exact bounded_mono each (by nlinarith) (by omega)
  | case2 n failed ih =>
    have before : n < BinaryExperiment.ratioIntegerBound r := by
      have : ¬BinaryExperiment.ratioIntegerBound r ≤ n := fun bound => failed ((ratioTest_iff r n).2 bound)
      omega
    have current := ratioTestOps_bounded r n S positive rBound (start.trans limit)
    have nfield := field_nat n
    have inc := naturalAdd_bounded n 1 (4*S) (by omega) (by omega) (by change 2 ≤ 4*S; omega)
    have tail := ih (by omega)
    exact bounded_mono (bounded_append
      (bounded_append (bounded_mono current (Nat.le_refl _) (by omega))
        (bounded_mono inc (Nat.le_refl _) (by omega))) tail) (by
          have sub : BinaryExperiment.ratioIntegerBound r-n = BinaryExperiment.ratioIntegerBound r-(n+1)+1 := by omega
          rw [sub]
          nlinarith) (Nat.le_refl _)

theorem exponentTestOps_bounded (budget : Rat) (N n S : Nat) (positive : 1 ≤ S)
    (budgetBound : field budget ≤ S) (number : N ≤ S) (counter : n ≤ S) :
    Bounded (exponentTestOps budget N n) (2*S+12) (128*S) := by
  have pn := field_power n
  have pN := field_power (N+1)
  have nf := field_nat N
  have nf' := field_nat n
  have c := field_mul 6 ((2 : Rat)^(N+1))
  have twoN := field_mul 2 (N : Rat)
  have threshold := field_mul (2*(N : Rat)) (6*(2 : Rat)^(N+1))
  have dyadic := field_mul ((2 : Rat)^n) budget
  rw [field_six] at c
  rw [field_two] at twoN
  have tail : Bounded
      [.natural N, .rational .mul 6 ((2 : Rat)^(N+1)), .rational .mul 2 (N : Rat),
        .rational .mul (2*(N : Rat)) (6*(2 : Rat)^(N+1)),
        .rational .mul ((2 : Rat)^n) budget,
        .rational .le (2*(N : Rat)*(6*(2 : Rat)^(N+1))) ((2 : Rat)^n*budget), .branch]
      7 (128*S) := by
    constructor
    · rfl
    · intro op member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Operation.width, field_six, field_two] <;> omega
  have oneTest := naturalLE_bounded 1 n (4*S) (by omega) (by change 2 ≤ 4*S; omega) (by omega)
  have powN := powerOps_bounded (N+1) (2*S) (by omega) (by omega)
  have pown := powerOps_bounded n S positive counter
  unfold exponentTestOps
  exact bounded_mono (bounded_append
    (bounded_append (bounded_append
      (bounded_mono powN (Nat.le_refl _) (by omega))
      (bounded_mono pown (Nat.le_refl _) (by omega)))
      (bounded_mono oneTest (Nat.le_refl _) (by omega))) tail) (by omega) (Nat.le_refl _)

theorem exponentOps_bounded (budget : Rat) (hbudget : 0 < budget) (N n S : Nat)
    (positive : 1 ≤ S) (budgetBound : field budget ≤ S) (number : N ≤ S)
    (limit : BinaryExperiment.quotaExponent budget N ≤ S)
    (start : n ≤ BinaryExperiment.quotaExponent budget N) :
    Bounded (exponentOps budget hbudget N n)
      ((BinaryExperiment.quotaExponent budget N-n+1)*(2*S+20)) (128*S) := by
  fun_induction exponentOps budget hbudget N n with
  | case1 n passed =>
    exact bounded_mono
      (exponentTestOps_bounded budget N n S positive budgetBound number (start.trans limit))
      (by nlinarith) (Nat.le_refl _)
  | case2 n failed ih =>
    have before : n < BinaryExperiment.quotaExponent budget N := by
      have : ¬BinaryExperiment.quotaExponent budget N ≤ n := fun bound =>
        failed ((exponentTest_iff budget hbudget N n).2 bound)
      omega
    have current := exponentTestOps_bounded budget N n S positive budgetBound number (start.trans limit)
    have nfield := field_nat n
    have inc := naturalAdd_bounded n 1 (4*S) (by omega) (by omega) (by change 2 ≤ 4*S; omega)
    have tail := ih (by omega)
    exact bounded_mono (bounded_append
      (bounded_append current (bounded_mono inc (Nat.le_refl _) (by omega))) tail) (by
        have sub : BinaryExperiment.quotaExponent budget N-n = BinaryExperiment.quotaExponent budget N-(n+1)+1 := by omega
        rw [sub]
        nlinarith) (Nat.le_refl _)

theorem quotaTestOps_bounded (e b m : Nat) (d : Rat) (n S : Nat) (positive : 1 ≤ S)
    (eb : e ≤ S) (bb : b ≤ S) (mb : m ≤ S) (db : field d ≤ S) (nb : n ≤ S) :
    Bounded (quotaTestOps e b m d n) 15 (128*S) := by
  have ef := field_nat e
  have bf := field_nat b
  have mf := field_nat m
  have nf := field_nat n
  have sum := field_add (e : Rat) (b : Rat)
  have r := field_mul 2 ((e : Rat)+b)
  have dn := field_mul d (n : Rat)
  have mm := field_mul (m : Rat) (m : Rat)
  have eight := field_mul 8 ((m : Rat)*m)
  have target := field_mul (e : Rat) (8*((m : Rat)*m))
  have dd := field_mul d d
  have ddn := field_mul (d*d) (n : Rat)
  rw [field_two] at r
  rw [field_eight] at eight
  constructor
  · rfl
  · intro op member
    simp only [quotaTestOps, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Operation.width, field_two, field_eight] <;> omega

theorem quotaOps_bounded (e b m : Nat) (d : Rat) (hd : 0 < d) (n S : Nat)
    (positive : 1 ≤ S) (eb : e ≤ S) (bb : b ≤ S) (mb : m ≤ S) (db : field d ≤ S)
    (limit : RootB234.Quota.quota e b m d ≤ S)
    (start : n ≤ RootB234.Quota.quota e b m d) :
    Bounded (quotaOps e b m d hd n) ((RootB234.Quota.quota e b m d-n+1)*19) (128*S) := by
  fun_induction quotaOps e b m d hd n with
  | case1 n passed =>
    exact bounded_mono (quotaTestOps_bounded e b m d n S positive eb bb mb db (start.trans limit))
      (by omega) (Nat.le_refl _)
  | case2 n failed ih =>
    have before : n < RootB234.Quota.quota e b m d := by
      have : ¬RootB234.Quota.quota e b m d ≤ n := fun bound =>
        failed ((quotaTest_iff e b m d hd n).2 bound)
      omega
    have current := quotaTestOps_bounded e b m d n S positive eb bb mb db (start.trans limit)
    have nfield := field_nat n
    have inc := naturalAdd_bounded n 1 (4*S) (by omega) (by omega) (by change 2 ≤ 4*S; omega)
    have tail := ih (by omega)
    exact bounded_mono (bounded_append
      (bounded_append current (bounded_mono inc (Nat.le_refl _) (by omega))) tail) (by
        have sub : RootB234.Quota.quota e b m d-n = RootB234.Quota.quota e b m d-(n+1)+1 := by omega
        rw [sub]
        omega) (Nat.le_refl _)

end RootPaper.Prep
