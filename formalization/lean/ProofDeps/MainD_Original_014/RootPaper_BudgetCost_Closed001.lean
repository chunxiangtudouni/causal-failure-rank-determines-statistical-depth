module
public import RootPaper_Prep_Closed006

/-! Two budget-specific algorithms. The operation lists are their erased
arithmetic schedules, not a language, VM, input oracle or runtime output.
Each listed primitive has the concrete native realization proved by Prep.
Guard selection and the final encoded result copy are explicitly charged. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.BudgetCost
open PaperProofs.Common.Native PaperProofs.Statistics
open RationalControllerComputation PSTRWordBool
open RootPaper.Prep

structure Calculation where
  value : Rat
  operations : List Operation
  admin : Nat

def Calculation.cost (result : Calculation) : Nat := arithmeticCost result.operations+result.admin

/-- One actual binary division, fixed call/return bookkeeping and one
linear traversal of the canonical result encoding. -/
def half (risk : Rat) : Calculation :=
  let value := risk/(2 : Rat)
  ⟨value,[.rational .div risk 2],8+(encode [.rational value]).length⟩

/-- The returned comparison bit selects exactly one existing candidate.
No positivity or nonzero-denominator qualification is imposed. -/
def badRisk (risk target : Rat) : Calculation :=
  let denominator := (2 : Rat)*target
  let ratio := risk/denominator
  let chooseQuarter := decide ((1/4 : Rat) ≤ ratio)
  let value := if chooseQuarter then (1/4 : Rat) else ratio
  ⟨value,[.rational .mul 2 target,.rational .div risk denominator,
    .rational .le (1/4) ratio,.branch],12+(encode [.rational value]).length⟩

def halfScale (risk : Rat) : Nat := field risk+1
def scale (risk target : Rat) : Nat := field risk+field target+1

/-- The concrete nativeRate is proved in frozen Prep. No cost/rate/width
constant is supplied by a caller. -/
def coefficient : Nat := 4*nativeRate*9^8+32

theorem coefficient_pos : 0 < coefficient := by unfold coefficient;omega

theorem half_value (risk : Rat) : (half risk).value=risk/2 := rfl

theorem badRisk_value (risk target : Rat) : (badRisk risk target).value=controllerBadRisk risk target := by
  by_cases selected : (1/4 : Rat) ≤ risk/(2*target)
  · simp only [badRisk,selected,decide_true,ite_true,controllerBadRisk,min_eq_left selected]
  · simp only [badRisk,selected,decide_false,Bool.false_eq_true,ite_false,controllerBadRisk,
      min_eq_right (le_of_not_ge selected)]

theorem half_schedule (risk : Rat) : (half risk).operations=[.rational .div risk 2] := rfl
theorem badRisk_schedule (risk target : Rat) :
    (badRisk risk target).operations=[.rational .mul 2 target,.rational .div risk (2*target),
      .rational .le (1/4) (risk/(2*target)),.branch] := rfl

theorem half_admin (risk : Rat) :
    (half risk).admin=8+(encode [.rational (half risk).value]).length := rfl
theorem badRisk_admin (risk target : Rat) :
    (badRisk risk target).admin=12+(encode [.rational (badRisk risk target).value]).length := rfl

theorem encoded_length (value : Rat) : (encode [.rational value]).length=2*field value+8 := by
  simpa only [field,RootB23.WordOddsBits.ratInput_fieldSize_eq,RootB23.WordOddsBits.width] using
    PA17TMRatArithmeticNativeSize007.singleton_output_length value

theorem field_quarter : field (1/(4 : Rat))=4 := by
  change RatInput.Encoder.fieldSize (1/(4 : Rat))=4
  rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
  norm_num [RootB23.WordOddsBits.width,natBits]

theorem half_output_width (risk : Rat) : field (half risk).value ≤ 4*halfScale risk := by
  have width := field_div risk 2
  rw [field_two] at width
  change field (risk/2) ≤ 4*(field risk+1)
  omega

theorem badRisk_operand_widths (risk target : Rat) :
    field (2*target) ≤ scale risk target+2 ∧
    field (risk/(2*target)) ≤ scale risk target+2 := by
  have denominator := field_mul 2 target
  rw [field_two] at denominator
  have ratio := field_div risk (2*target)
  unfold scale
  omega

theorem badRisk_output_width (risk target : Rat) :
    field (badRisk risk target).value ≤ 4*scale risk target := by
  have ratio := (badRisk_operand_widths risk target).2
  have positive : 1 ≤ scale risk target := by unfold scale;omega
  dsimp only [badRisk]
  split_ifs
  · rw [field_quarter]
    omega
  · omega

theorem half_bounded (risk : Rat) : Bounded (half risk).operations 4 (8*halfScale risk) := by
  constructor
  · change 1 ≤ 4;decide
  · intro op member
    have same : op=.rational .div risk 2 := by simpa only [half_schedule,List.mem_singleton] using member
    subst op
    simp only [Operation.width,field_two,halfScale]
    omega

theorem badRisk_bounded (risk target : Rat) :
    Bounded (badRisk risk target).operations 4 (8*scale risk target) := by
  have widths := badRisk_operand_widths risk target
  have positive : 1 ≤ scale risk target := by unfold scale;omega
  constructor
  · rfl
  · intro op member
    rw [badRisk_schedule] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · simp only [Operation.width,field_two]
      unfold scale
      omega
    · simp only [Operation.width]
      have denominator := field_mul 2 target
      rw [field_two] at denominator
      unfold scale at *
      omega
    · simp only [Operation.width,field_quarter]
      omega
    · change 1 ≤ 8*scale risk target
      omega

theorem half_realized (risk : Rat) : ∀ op ∈ (half risk).operations,op.Realized :=
  fun op _ => operation_realized op
theorem badRisk_realized (risk target : Rat) : ∀ op ∈ (badRisk risk target).operations,op.Realized :=
  fun op _ => operation_realized op

private theorem result_widths {ops : List Operation} {S : Nat}
    (positive : 1 ≤ S) (bounded : Bounded ops 4 (8*S)) :
    ∀ op ∈ ops,op.resultWidth ≤ 36*S := by
  intro op member
  have old := resultWidth_bound op
  have operand := bounded.2 op member
  omega

theorem half_result_widths (risk : Rat) :
    ∀ op ∈ (half risk).operations,op.resultWidth ≤ 36*halfScale risk :=
  result_widths (by unfold halfScale;omega) (half_bounded risk)
theorem badRisk_result_widths (risk target : Rat) :
    ∀ op ∈ (badRisk risk target).operations,op.resultWidth ≤ 36*scale risk target :=
  result_widths (by unfold scale;omega) (badRisk_bounded risk target)

theorem half_admin_bound (risk : Rat) : (half risk).admin ≤ 32*halfScale risk := by
  have width := half_output_width risk
  have positive : 1 ≤ halfScale risk := by unfold halfScale;omega
  rw [half_admin,encoded_length]
  omega

theorem badRisk_admin_bound (risk target : Rat) : (badRisk risk target).admin ≤ 32*scale risk target := by
  have width := badRisk_output_width risk target
  have positive : 1 ≤ scale risk target := by unfold scale;omega
  rw [badRisk_admin,encoded_length]
  omega

private theorem total_bound (result : Calculation) (S : Nat) (positive : 1 ≤ S)
    (bounded : Bounded result.operations 4 (8*S)) (admin : result.admin ≤ 32*S) :
    result.cost ≤ coefficient*S^8 := by
  have arithmetic := bounded_arithmeticCost bounded
  have input : 8*S+1 ≤ 9*S := by omega
  have power := Nat.pow_le_pow_left input 8
  have larger : S ≤ S^8 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1 ≤ 8)
  have arith : arithmeticCost result.operations ≤ (4*nativeRate*9^8)*S^8 := by
    exact arithmetic.trans ((Nat.mul_le_mul_left (4*nativeRate) power).trans_eq (by ring))
  have adm := admin.trans (Nat.mul_le_mul_left 32 larger)
  unfold Calculation.cost coefficient
  rw [Nat.add_mul]
  exact Nat.add_le_add arith adm

theorem half_cost (risk : Rat) : (half risk).cost ≤ coefficient*(halfScale risk)^8 :=
  total_bound (half risk) _ (by unfold halfScale;omega) (half_bounded risk) (half_admin_bound risk)

theorem badRisk_cost (risk target : Rat) : (badRisk risk target).cost ≤ coefficient*(scale risk target)^8 :=
  total_bound (badRisk risk target) _ (by unfold scale;omega) (badRisk_bounded risk target) (badRisk_admin_bound risk target)

/-- Half also has the shared two-operand scale requested by both consumers. -/
theorem half_pair_cost (risk target : Rat) : (half risk).cost ≤ coefficient*(scale risk target)^8 :=
  (half_cost risk).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold halfScale scale;omega) 8))

theorem half_closed (risk : Rat) :
    (half risk).value=risk/2 ∧
    (∀ op ∈ (half risk).operations,op.Realized) ∧
    Bounded (half risk).operations 4 (8*halfScale risk) ∧
    (∀ op ∈ (half risk).operations,op.resultWidth ≤ 36*halfScale risk) ∧
    field (half risk).value ≤ 4*halfScale risk ∧
    (half risk).admin ≤ 32*halfScale risk ∧
    (half risk).cost ≤ coefficient*(halfScale risk)^8 :=
  ⟨half_value risk,half_realized risk,half_bounded risk,half_result_widths risk,
    half_output_width risk,half_admin_bound risk,half_cost risk⟩

theorem badRisk_closed (risk target : Rat) :
    (badRisk risk target).value=controllerBadRisk risk target ∧
    (∀ op ∈ (badRisk risk target).operations,op.Realized) ∧
    Bounded (badRisk risk target).operations 4 (8*scale risk target) ∧
    (∀ op ∈ (badRisk risk target).operations,op.resultWidth ≤ 36*scale risk target) ∧
    field (badRisk risk target).value ≤ 4*scale risk target ∧
    (badRisk risk target).admin ≤ 32*scale risk target ∧
    (badRisk risk target).cost ≤ coefficient*(scale risk target)^8 :=
  ⟨badRisk_value risk target,badRisk_realized risk target,badRisk_bounded risk target,
    badRisk_result_widths risk target,badRisk_output_width risk target,badRisk_admin_bound risk target,badRisk_cost risk target⟩

end RootPaper.BudgetCost

#print axioms RootPaper.BudgetCost.half_closed
#print axioms RootPaper.BudgetCost.badRisk_closed
#print axioms RootPaper.BudgetCost.half_pair_cost
