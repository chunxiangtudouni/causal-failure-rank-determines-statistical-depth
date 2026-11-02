module

public import RootPaper_Prep_Total005
public import RootPaper_Scalar_Closed001
public import RootB234_PrepExponent_NatToRatPublic008

/-! Actual binary primitive fees for the paper preparation schedule.
The comparison fee includes the concrete primitive-clock sum. No rate,
polynomial, runtime fuel or complexity certificate is a caller premise. -/

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

def binaryPower : Nat → Rat
  | 0 => 1
  | n+1 => binaryPower n*2

theorem binaryPower_eq (n : Nat) : binaryPower n = (2 : Rat)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [binaryPower, ih, pow_succ]

/-- This is the executable multiplication sequence expanded by powerOps. -/
theorem ratioTest_binary (r : Rat) (n : Nat) :
    (decide (r ≤ binaryPower n) && decide (1/r ≤ binaryPower n)) = ratioTest r n := by
  rw [binaryPower_eq]
  rfl

theorem exponentTest_binary (budget : Rat) (N n : Nat) :
    (decide (1 ≤ n) && decide ((2*(N : Rat)*(6*binaryPower (N+1))) ≤ binaryPower n*budget)) =
      exponentTest budget N n := by
  simp only [binaryPower_eq, exponentTest, referenceQuotaConstant]
  rfl

theorem absolute_selection (q : Rat) : (if decide (0 ≤ q) then q else 0-q) = |q| := by
  by_cases sign : 0 ≤ q
  · simp only [sign, decide_true, ite_true, abs_of_nonneg sign]
  · simp only [sign, decide_false, Bool.false_eq_true, ite_false, zero_sub,
      abs_of_neg (lt_of_not_ge sign)]

theorem maximum_selection (a b : Nat) : (if decide (a ≤ b) then b else a) = max a b := by
  by_cases h : a ≤ b
  · simp [h]
  · simp [h, max_eq_left (le_of_not_ge h)]

theorem minimum_selection (a b : Nat) : (if decide (a ≤ b) then a else b) = min a b := by
  by_cases h : a ≤ b
  · simp [h]
  · simp [h, min_eq_right (le_of_not_ge h)]

theorem natural_comparison (a b : Nat) : decide ((a : Rat) ≤ b) = decide (a ≤ b) := by
  simp only [Nat.cast_le]

theorem natural_addition (a b : Nat) : (a : Rat)+(b : Rat) = ((a+b : Nat) : Rat) := by
  simp only [Nat.cast_add]

def natBackground : RatInput.Stack → List Bool := fun _ => []
def natPacket (n : Nat) : List Bool := B23_4_RatWordPrep.NatField.packet n []
def natScale (n : Nat) : Nat := RootB234.PrepExponent.NatToRat.scale natBackground n []

def naturalFee (n : Nat) : Nat :=
  6045*(natScale n)^2+(natPacket n).length+(RatInput.Encoder.packet (n : Rat) []).length

def Operation.nativeFee : Operation → Nat
  | .rational .add x y | .rational .sub x y =>
      (RatAddSub.addSubCoefficient+3)*((RootPaper.Scalar.pairInput x y).length+1)^4
  | .rational .mul x y =>
      (RatMulDiv.mulCoefficient+3)*((RootPaper.Scalar.pairInput x y).length+1)^4
  | .rational .div x y =>
      (RatMulDiv.divCoefficient+3)*((RootPaper.Scalar.pairInput x y).length+1)^4
  | .rational .le x y =>
      RootPaper.Scalar.comparisonCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^8
  | .natural n => naturalFee n
  | .branch => 1

def arithmeticCost (ops : List Operation) : Nat := (ops.map Operation.nativeFee).sum

def nativeRate : Nat :=
  (RatAddSub.addSubCoefficient+RatMulDiv.mulCoefficient+RatMulDiv.divCoefficient+
    RootPaper.Scalar.comparisonCoefficient+1000000000)*64^8

theorem nativeRate_pos : 0 < nativeRate := by
  unfold nativeRate
  exact Nat.mul_pos (by omega) (by decide)

theorem pair_bits (x y : Rat) :
    (RootPaper.Scalar.pairInput x y).length = 2*(field x+field y)+14 := by
  have size := RootPaper.Scalar.pair_input_bits x y
  simp only [PA17TMRatArithmeticNativeSize007.inputBits] at size
  simp only [field, RootB23.WordOddsBits.ratInput_fieldSize_eq, RootB23.WordOddsBits.width]
  omega

theorem pair_bits_le (x y : Rat) :
    (RootPaper.Scalar.pairInput x y).length+1 ≤ 16*(field x+field y+2) := by
  rw [pair_bits]
  omega

theorem natPacket_length (n : Nat) : (natPacket n).length = 2*natBits n+2 := by
  have h := RootB234.ECost.natural_packet_length n []
  simpa only [natPacket, RootB234.ECost.raw, PSTRTMNatValue017.rawPayload,
    List.length_ofFn, List.length_nil, Nat.add_zero] using h

theorem natScale_bound (n : Nat) : natScale n ≤ 64*(field (n : Rat)+1) := by
  have each : ∀ slot,
      (RootB234.PrepExponent.NatToRat.bank natBackground (natPacket n) [] [] [] slot).length ≤ (natPacket n).length := by
    intro slot
    unfold RootB234.PrepExponent.NatToRat.bank natBackground
    split_ifs
    all_goals first | exact Nat.le_refl _ | exact Nat.zero_le _
  have mass := RatInput.Encoder.occupied_bound _ _ each
  change natScale n ≤ _
  unfold natScale RootB234.PrepExponent.NatToRat.scale RootB234.PrepExponent.NatToRat.initialMass
  change RatInput.occupied (RootB234.PrepExponent.NatToRat.bank natBackground (natPacket n) [] [] [])+1 ≤ _
  rw [natPacket_length, nat_field_eq] at *
  omega

/-- An already-closed binary cast, with actual charged clock cost and
input/result copies. This depends on digit length, never the Nat value. -/
theorem natural_closed (n : Nat) :
    ∃ run : List (RootB234.PrepExponent.NatToRat.State Unit),
      RootB234.PrepExponent.NatToRat.Facts natBackground ((),false,false) n [] run ∧
      run.length+RootB234.PrepExponent.NatToRat.traceClockSum run+
        (natPacket n).length+(RatInput.Encoder.packet (n : Rat) []).length ≤ naturalFee n := by
  obtain ⟨run,facts⟩ := RootB234.PrepExponent.NatToRat.actual_bounded natBackground ((),false,false) n []
  exact ⟨run, facts, Nat.add_le_add_right
    (Nat.add_le_add_right (RootB234.PrepExponent.NatToRat.chargedCost_le facts) _) _⟩

/-- For each scheduled operation, a concrete previously-proved binary
algorithm supplies exactly its mathematical value and pays its copy/read
costs. This Prop is proved here; it is never an input to preparation. -/
def Operation.Realized (op : Operation) : Prop :=
  match op with
  | .rational .add x y =>
      computes (PA17TMRatArithmeticAddSubController075.addSubMachine false)
        (RootPaper.Scalar.pairInput x y) (encode [.rational (x+y)])
        (RatAddSub.addSubCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4)
        (RatAddSub.addSubCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4) ∧
      RatAddSub.addSubCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4+
        (RootPaper.Scalar.pairInput x y).length+(encode [.rational (x+y)]).length ≤ op.nativeFee
  | .rational .sub x y =>
      computes (PA17TMRatArithmeticAddSubController075.addSubMachine true)
        (RootPaper.Scalar.pairInput x y) (encode [.rational (x-y)])
        (RatAddSub.addSubCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4)
        (RatAddSub.addSubCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4) ∧
      RatAddSub.addSubCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4+
        (RootPaper.Scalar.pairInput x y).length+(encode [.rational (x-y)]).length ≤ op.nativeFee
  | .rational .mul x y =>
      computes RatMulDiv.mulSource (RootPaper.Scalar.pairInput x y) (encode [.rational (x*y)])
        (RatMulDiv.mulCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4)
        (RatMulDiv.mulCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4) ∧
      RatMulDiv.mulCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4+
        (RootPaper.Scalar.pairInput x y).length+(encode [.rational (x*y)]).length ≤ op.nativeFee
  | .rational .div x y =>
      computes RatMulDiv.divSource (RootPaper.Scalar.pairInput x y) (encode [.rational (x/y)])
        (RatMulDiv.divCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4)
        (RatMulDiv.divCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4) ∧
      RatMulDiv.divCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4+
        (RootPaper.Scalar.pairInput x y).length+(encode [.rational (x/y)]).length ≤ op.nativeFee
  | .rational .le x y =>
      ∃ (path : List (RatCmp.State Unit)) (final : RatCmp.State Unit),
        RatCmp.Facts (RatCmp.program .halt) RatCmp.coefficient RatCmp.degree ()
          default default default (fun _=>[]) x y path final ∧
        final.stk 3=[decide (x≤y)] ∧
        path.length+(path.dropLast.map RootPaper.Scalar.comparisonClock).sum+
          (RootPaper.Scalar.pairInput x y).length+1 ≤ op.nativeFee
  | .natural n =>
      ∃ run : List (RootB234.PrepExponent.NatToRat.State Unit),
        RootB234.PrepExponent.NatToRat.Facts natBackground ((),false,false) n [] run ∧
        run.length+RootB234.PrepExponent.NatToRat.traceClockSum run+
          (natPacket n).length+(RatInput.Encoder.packet (n : Rat) []).length ≤ op.nativeFee
  | .branch => True

theorem operation_realized (op : Operation) : op.Realized := by
  cases op with
  | branch => trivial
  | natural n => exact natural_closed n
  | rational kind x y =>
    cases kind with
    | add =>
      have h := RootPaper.Scalar.add_sub_closed false x y
      exact ⟨h.1,h.2.2⟩
    | sub =>
      have h := RootPaper.Scalar.add_sub_closed true x y
      exact ⟨h.1,h.2.2⟩
    | mul =>
      have h := RootPaper.Scalar.mul_closed x y
      exact ⟨h.1,h.2.2⟩
    | div =>
      have h := RootPaper.Scalar.div_closed x y
      exact ⟨h.1,h.2.2⟩
    | le => exact RootPaper.Scalar.rational_le_closed x y

def Operation.resultWidth : Operation → Nat
  | .rational .add x y => field (x+y)
  | .rational .sub x y => field (x-y)
  | .rational .mul x y => field (x*y)
  | .rational .div x y => field (x/y)
  | .rational .le _ _ => 2
  | .natural n => field (n : Rat)
  | .branch => 1

/-- These are the same-run internal bit-space/stack-digit bounds of the
closed primitives: arithmetic native space, comparison internal nodes, and
the Nat cast's internal nodes. They include more than canonical outputs. -/
def Operation.internalWidth : Operation → Nat
  | .rational .add x y | .rational .sub x y =>
      RatAddSub.addSubCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4
  | .rational .mul x y => RatMulDiv.mulCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4
  | .rational .div x y => RatMulDiv.divCoefficient*((RootPaper.Scalar.pairInput x y).length+1)^4
  | .rational .le x y => RatCmp.scale RatCmp.coefficient RatCmp.degree (fun _=>[]) x y+3
  | .natural n => 57*natScale n
  | .branch => 1

theorem internalWidth_le_fee (op : Operation) : op.internalWidth ≤ op.nativeFee := by
  cases op with
  | branch => exact Nat.le_refl _
  | natural n =>
    have one : 1 ≤ natScale n := by unfold natScale RootB234.PrepExponent.NatToRat.scale; omega
    have square : natScale n ≤ natScale n^2 := by nlinarith
    simp only [Operation.internalWidth, Operation.nativeFee, naturalFee]
    nlinarith
  | rational kind x y =>
    cases kind with
    | add | sub | mul | div =>
      simp only [Operation.internalWidth, Operation.nativeFee]
      exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    | le =>
      let S := (RootPaper.Scalar.pairInput x y).length+1
      have positive : 1 ≤ S := by unfold S; omega
      have one8 : 1 ≤ S^8 := one_le_pow₀ positive
      have power : S^4 ≤ S^8 := Nat.pow_le_pow_right positive (by decide)
      have outside : IsolatedRat.outside (fun _ : RatInput.Stack=>[]) = 0 := by rfl
      have factor : RatCmp.coefficient+1027 ≤ RootPaper.Scalar.comparisonCoefficient := by
        unfold RootPaper.Scalar.comparisonCoefficient
        nlinarith
      have scale : RatCmp.scale RatCmp.coefficient RatCmp.degree (fun _=>[]) x y+3 ≤
          (RatCmp.coefficient+1027)*S^8 := by
        simp only [RatCmp.scale, outside, Nat.zero_add, Nat.mul_one, RatCmp.degree_eq_four]
        change 1024+RatCmp.coefficient*S^4+3 ≤ _
        have multiplied := Nat.mul_le_mul_left RatCmp.coefficient power
        nlinarith
      exact scale.trans (Nat.mul_le_mul_right _ factor)

theorem resultWidth_bound (op : Operation) : op.resultWidth ≤ 4*(op.width+1) := by
  cases op with
  | branch => decide
  | natural n => simp only [Operation.resultWidth, Operation.width]; omega
  | rational kind x y =>
    have add := field_add x y
    have sub := field_sub x y
    have mul := field_mul x y
    have div := field_div x y
    cases kind <;> simp only [Operation.resultWidth, Operation.width] <;> omega

theorem nativeFee_bound (op : Operation) : op.nativeFee ≤ nativeRate*(op.width+1)^8 := by
  cases op with
  | branch =>
    simp only [Operation.nativeFee, Operation.width]
    have positive := nativeRate_pos
    nlinarith
  | natural n =>
    have scale := natScale_bound n
    have packet := natPacket_length n
    have result := RatInput.Encoder.packet_length (n : Rat) []
    change (RatInput.Encoder.packet (n : Rat) []).length = 2*field (n : Rat)+6+0 at result
    have widthPositive : 1 ≤ field (n : Rat)+2 := by omega
    have power : (field (n : Rat)+2)^2 ≤ (field (n : Rat)+2)^8 :=
      Nat.pow_le_pow_right widthPositive (by decide)
    have linear : field (n : Rat)+2 ≤ (field (n : Rat)+2)^2 := by nlinarith
    have size : naturalFee n ≤ 1000000000*(field (n : Rat)+2)^2 := by
      unfold naturalFee
      rw [packet, result, nat_field_eq] at *
      have square := Nat.pow_le_pow_left scale 2
      nlinarith
    have rate : 1000000000 ≤ nativeRate := by
      unfold nativeRate
      have mul : 1 ≤ 64^8 := by decide
      nlinarith
    change naturalFee n ≤ nativeRate*(field (n : Rat)+1+1)^8
    simpa only [Nat.add_assoc] using size.trans (Nat.mul_le_mul rate power)
  | rational kind x y =>
    have input := pair_bits_le x y
    have one : 1 ≤ (RootPaper.Scalar.pairInput x y).length+1 := by omega
    have p4 : ((RootPaper.Scalar.pairInput x y).length+1)^4 ≤
        (16*(field x+field y+2))^8 := by
      exact (Nat.pow_le_pow_right one (by decide : 4 ≤ 8)).trans (Nat.pow_le_pow_left input 8)
    have p8 := Nat.pow_le_pow_left input 8
    have mulRate : (RatMulDiv.mulCoefficient+3)*16^8 ≤ nativeRate := by unfold nativeRate; nlinarith
    have divRate : (RatMulDiv.divCoefficient+3)*16^8 ≤ nativeRate := by unfold nativeRate; nlinarith
    have addRate : (RatAddSub.addSubCoefficient+3)*16^8 ≤ nativeRate := by unfold nativeRate; nlinarith
    have cmpRate : RootPaper.Scalar.comparisonCoefficient*16^8 ≤ nativeRate := by unfold nativeRate; nlinarith
    have absorb (c d : Nat) (rate : c*16^8 ≤ nativeRate)
        (power : ((RootPaper.Scalar.pairInput x y).length+1)^d ≤ (16*(field x+field y+2))^8) :
        c*((RootPaper.Scalar.pairInput x y).length+1)^d ≤ nativeRate*(field x+field y+2)^8 := by
      calc
        _ ≤ c*(16*(field x+field y+2))^8 := Nat.mul_le_mul_left c power
        _ = (c*16^8)*(field x+field y+2)^8 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ rate
    cases kind with
    | add | sub => exact absorb (RatAddSub.addSubCoefficient+3) 4 addRate p4
    | mul => exact absorb (RatMulDiv.mulCoefficient+3) 4 mulRate p4
    | div => exact absorb (RatMulDiv.divCoefficient+3) 4 divRate p4
    | le => exact absorb RootPaper.Scalar.comparisonCoefficient 8 cmpRate p8

theorem bounded_arithmeticCost {ops : List Operation} {count width : Nat} (h : Bounded ops count width) :
    arithmeticCost ops ≤ count*nativeRate*(width+1)^8 := by
  have summed : arithmeticCost ops ≤ ops.length*(nativeRate*(width+1)^8) := by
    unfold arithmeticCost
    have bound := List.sum_le_length_nsmul (ops.map Operation.nativeFee) (nativeRate*(width+1)^8) (by
      intro cost member
      obtain ⟨op, present, rfl⟩ := List.mem_map.mp member
      exact (nativeFee_bound op).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (Nat.add_le_add_right (h.2 op present) 1) 8)))
    simpa only [List.length_map, smul_eq_mul] using bound
  exact summed.trans ((Nat.mul_le_mul_right _ h.1).trans_eq (by ring))

/-- Fixed coefficient and degree precede every original input. The charge
is the sum of the concrete binary primitive fees, including operand and
result copies; it is not the output length or the number of syntax nodes. -/
theorem paper_preparation_arithmetic (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) :
    arithmeticCost (preparationOps input C budget positive) ≤
      (1000000*nativeRate*4097^8)*(arithmeticScale input C budget)^12 := by
  let P := arithmeticScale input C budget
  have one : 1 ≤ P := by unfold P arithmeticScale; omega
  have bound := bounded_arithmeticCost (original_preparationOps_bounded I input C budget positive)
  have linear : 4096*P+1 ≤ 4097*P := by omega
  have powered := Nat.pow_le_pow_left linear 8
  exact bound.trans ((Nat.mul_le_mul_left (1000000*P^4*nativeRate) powered).trans_eq (by
    dsimp only [P]
    ring))

/-- The paper returns these numerical resources and the original Boolean
qualification. The historical Bool encoding is only a pure corollary. -/
structure NumericalPreparation (I : Instance) where
  exponent : Nat
  rows : List (I.Stage × StageResult)
  qualification : Bool

def numericalPreparation {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) : NumericalPreparation I :=
  let e := exponentSearch budget positive I.stageCount 1
  let rows := (List.finRange I.stageCount).map (fun stage => (stage, prepareStage (input.experiment stage) e))
  ⟨e,rows,qualify C rows⟩

theorem numericalPreparation_eq (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) :
    numericalPreparation input C budget positive =
      ⟨computedExponent (I:=I) budget, originalRows input budget, numericQualification input C budget⟩ := by
  have epositive : 1 ≤ BinaryExperiment.quotaExponent budget I.stageCount := le_max_left _ _
  have exactE : exponentSearch budget positive I.compatibility.length 1 = computedExponent (I:=I) budget := by
    change exponentSearch budget positive I.stageCount 1 = _
    rw [exponentSearch_eq, max_eq_right epositive]
    rfl
  have qualified := qualification_eq I input C budget
  simp only [Instance.stageCount] at qualified
  simp only [numericalPreparation, Instance.stageCount]
  rw [exactE, qualified]
  rfl

theorem paper_preparation_closed :
    ∃ coefficient degree : Nat, 0 < coefficient ∧ 0 < degree ∧
      ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) (positive : 0 < budget),
        numericalPreparation input C budget positive =
          ⟨computedExponent (I:=I) budget, originalRows input budget, numericQualification input C budget⟩ ∧
        preparation input C budget positive = preparationOutput input C budget ∧
        (preparationOps input C budget positive).length ≤ coefficient*(arithmeticScale input C budget)^degree ∧
        (∀ op ∈ preparationOps input C budget positive,
          op.Realized ∧ op.width ≤ coefficient*(arithmeticScale input C budget)^degree ∧
          op.resultWidth ≤ coefficient*(arithmeticScale input C budget)^degree ∧
          op.internalWidth ≤ coefficient*(arithmeticScale input C budget)^degree) ∧
        arithmeticCost (preparationOps input C budget positive) ≤
          coefficient*(arithmeticScale input C budget)^degree := by
  let coefficient := 1000000*nativeRate*4097^8+1000000+16388
  have feeLE : 1000000*nativeRate*4097^8 ≤ coefficient :=
    (Nat.le_add_right _ 1000000).trans (Nat.le_add_right _ 16388)
  have countLE : 1000000 ≤ coefficient :=
    (Nat.le_add_left 1000000 (1000000*nativeRate*4097^8)).trans (Nat.le_add_right _ 16388)
  have resultLE : 16388 ≤ coefficient := Nat.le_add_left 16388 _
  have operandLE : 4096 ≤ coefficient := (by decide : 4096 ≤ 16388).trans resultLE
  refine ⟨coefficient,12,lt_of_lt_of_le (by decide : 0 < 16388) resultLE,by decide,?_⟩
  intro I input C budget positive
  let P := arithmeticScale input C budget
  have one : 1 ≤ P := Nat.succ_le_succ (Nat.zero_le _)
  have power4 : P^4 ≤ P^12 := Nat.pow_le_pow_right one (by decide)
  have power1 : P ≤ P^12 := by simpa only [pow_one] using Nat.pow_le_pow_right one (by decide : 1 ≤ 12)
  have bounded := original_preparationOps_bounded I input C budget positive
  refine ⟨numericalPreparation_eq I input C budget positive,preparation_eq I input C budget positive,?_,?_,?_⟩
  · exact bounded.1.trans (Nat.mul_le_mul countLE power4)
  · intro op member
    have operand := bounded.2 op member
    have result := resultWidth_bound op
    refine ⟨operation_realized op,?_,?_,?_⟩
    · exact operand.trans (Nat.mul_le_mul operandLE power1)
    · have rBound : op.resultWidth ≤ 16388*P := by
        have operandBound : op.width ≤ 4096*P := operand
        have scaled := Nat.mul_le_mul_left 4 (Nat.add_le_add_right operandBound 1)
        have four : 4 ≤ 4*P := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 4 one
        apply (result.trans scaled).trans
        calc
          4*(4096*P+1) = 4*(4096*P)+4 := by ring
          _ ≤ 4*(4096*P)+4*P := Nat.add_le_add_left four _
          _ = 16388*P := by ring
      exact rBound.trans (Nat.mul_le_mul resultLE power1)
    · have single : op.nativeFee ≤ arithmeticCost (preparationOps input C budget positive) :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨op, member, rfl⟩)
      exact (internalWidth_le_fee op).trans (single.trans
        ((paper_preparation_arithmetic I input C budget positive).trans
          (Nat.mul_le_mul_right _ feeLE)))
  · exact (paper_preparation_arithmetic I input C budget positive).trans
      (Nat.mul_le_mul_right _ feeLE)

end RootPaper.Prep

#print axioms RootPaper.Prep.paper_preparation_closed
