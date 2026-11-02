module
public import Structure.PA17_TM_RatArithmetic_RatDivFields_066a
public import Structure.PA17_TM_RatArithmetic_ZeroCarry_058e

/-! Pure fields for one fixed addition/subtraction mode, before all x,y.
Both saturated differences are genuine native results. The equal-magnitude
opposite-sign case may select either raw sign; real U-zero repair clears it.
Finite memory maps below interpret future actual control transitions only. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSignedSumFields072

open PA17TMRatArithmeticSemantics001 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticNativeSize007 PA17TMRatArithmeticNativeCache030
open PA17TMRatArithmeticWideCache045 PSTRTMArithmetic008 PSTRTMLength004

def target (subtract : Bool) (x y : Rat) : Rat := if subtract then x-y else x+y
def leftMagnitude (x y : Rat) : Nat := x.num.natAbs*y.den
def rightMagnitude (x y : Rat) : Nat := x.den*y.num.natAbs
def commonDenominator (x y : Rat) : Nat := x.den*y.den
def leftDifference (x y : Rat) : Nat := leftMagnitude x y-rightMagnitude x y
def rightDifference (x y : Rat) : Nat := rightMagnitude x y-leftMagnitude x y
def effectiveSign (subtract : Bool) (y : Rat) : Bool := Bool.xor (sign y) subtract
def sameSigns (subtract : Bool) (x y : Rat) : Bool := sign x==effectiveSign subtract y
def sumMagnitude (subtract : Bool) (x y : Rat) : Nat :=
  if sameSigns subtract x y then leftMagnitude x y+rightMagnitude x y
  else leftDifference x y+rightDifference x y
def negativeChoice (sx sy pZero : Bool) : Bool := if sx==sy then sx else if pZero then sy else sx
def sumNegative (subtract : Bool) (x y : Rat) : Bool :=
  negativeChoice (sign x) (effectiveSign subtract y) (decide (leftDifference x y=0))
def normalizer (subtract : Bool) (x y : Rat) : Nat := Nat.gcd (sumMagnitude subtract x y) (commonDenominator x y)
def quotientNumerator (subtract : Bool) (x y : Rat) : Nat := sumMagnitude subtract x y/normalizer subtract x y
def quotientDenominator (subtract : Bool) (x y : Rat) : Nat := commonDenominator x y/normalizer subtract x y
def zeroRepairedSign (negative : Bool) (u : Nat) : Bool := if u=0 then false else negative
def addLeft (subtract : Bool) (x y : Rat) : Nat :=
  if sameSigns subtract x y then leftMagnitude x y else leftDifference x y
def addRight (subtract : Bool) (x y : Rat) : Nat :=
  if sameSigns subtract x y then rightMagnitude x y else rightDifference x y

theorem commonDenominator_pos (x y : Rat) : 0<commonDenominator x y := Nat.mul_pos x.den_pos y.den_pos

/-- Same signed-addition identity as frozen001, with TWO actual saturated
differences and a P-zero choice in place of a free comparison result. -/
theorem signed_choice (sx sy : Bool) (m n : Nat) :
    signed (negativeChoice sx sy (decide (m-n=0)))
      (if sx==sy then m+n else (m-n)+(n-m))=signed sx m+signed sy n := by
  by_cases hmn : m≤n
  · have hp : m-n=0 := Nat.sub_eq_zero_of_le hmn
    cases sx <;> cases sy <;> simp [negativeChoice,signed,hp] <;> omega
  · have hn : n-m=0 := Nat.sub_eq_zero_of_le (by omega)
    have hp : m-n≠0 := by omega
    cases sx <;> cases sy <;> simp [negativeChoice,signed,hn,hp] <;> omega

theorem signed_effective (subtract sy : Bool) (n : Nat) :
    signed (Bool.xor sy subtract) n=if subtract then -(signed sy n) else signed sy n := by
  cases subtract <;> cases sy <;> simp [signed]

theorem signed_numerator (subtract : Bool) (x y : Rat) :
    signed (sumNegative subtract x y) (sumMagnitude subtract x y)=
      if subtract then subNum x y else addNum x y := by
  have left : signed (sign x) (leftMagnitude x y)=x.num*(y.den : Int) := by
    rw [leftMagnitude,signed_scale]
    exact congrArg (fun z : Int => z*(y.den : Int)) (signed_rat_num x)
  have right : signed (sign y) (rightMagnitude x y)=y.num*(x.den : Int) := by
    rw [rightMagnitude,Nat.mul_comm,signed_scale]
    exact congrArg (fun z : Int => z*(x.den : Int)) (signed_rat_num y)
  have h := signed_choice (sign x) (effectiveSign subtract y) (leftMagnitude x y) (rightMagnitude x y)
  change signed (sumNegative subtract x y) (sumMagnitude subtract x y)=_ at h
  rw [left] at h
  simp only [effectiveSign,signed_effective,right] at h
  cases subtract <;> simpa only [Bool.false_eq_true,ite_false,ite_true,subNum,addNum,sub_eq_add_neg] using h

theorem signed_value (subtract : Bool) (x y : Rat) :
    mkRat (signed (sumNegative subtract x y) (sumMagnitude subtract x y)) (commonDenominator x y)=target subtract x y := by
  rw [signed_numerator]
  cases subtract
  · exact add_value x y
  · exact sub_value x y

theorem actual_fields (subtract : Bool) (x y : Rat) (r e g u v : Nat)
    (hr : r=sumMagnitude subtract x y) (he : e=commonDenominator x y)
    (hg : g=Nat.gcd r e) (hu : u=r/g) (hv : v=e/g) :
    u=(target subtract x y).num.natAbs ∧ v=(target subtract x y).den ∧
      zeroRepairedSign (sumNegative subtract x y) u=sign (target subtract x y) := by
  have value : mkRat (signed (sumNegative subtract x y) r) e=target subtract x y := by
    rw [hr,he]
    exact signed_value subtract x y
  have he0 : e≠0 := by rw [he];exact Nat.ne_of_gt (commonDenominator_pos x y)
  obtain ⟨hn,hd,hs⟩ := quotient_result_fields (sumNegative subtract x y) r e g u v
    (decide (u=0)) false (target subtract x y) value hg hu hv rfl (by simp [he0])
  have repair : zeroRepairedSign (sumNegative subtract x y) u=
      repairedSign (sumNegative subtract x y) (decide (u=0)) false := by
    by_cases hz : u=0 <;> simp [zeroRepairedSign,repairedSign,hz]
  exact ⟨by simpa only [resultMagnitude,Bool.false_eq_true,ite_false] using hn.symm,
    by simpa only [resultDenominator,Bool.false_eq_true,ite_false] using hd.symm,
    repair.trans hs.symm⟩

theorem pipeline_fields (subtract : Bool) (x y : Rat) :
    quotientNumerator subtract x y=(target subtract x y).num.natAbs ∧
    quotientDenominator subtract x y=(target subtract x y).den ∧
    zeroRepairedSign (sumNegative subtract x y) (quotientNumerator subtract x y)=sign (target subtract x y) :=
  actual_fields subtract x y (sumMagnitude subtract x y) (commonDenominator x y) (normalizer subtract x y)
    (quotientNumerator subtract x y) (quotientDenominator subtract x y) rfl rfl rfl rfl rfl

theorem actual_add_arguments (subtract : Bool) (x y : Rat) :
    addLeft subtract x y+addRight subtract x y=sumMagnitude subtract x y := by
  cases h : sameSigns subtract x y <;> simp [addLeft,addRight,sumMagnitude,h]

theorem cancellation_fields (subtract : Bool) (x y : Rat) (hz : target subtract x y=0) :
    quotientNumerator subtract x y=0 ∧ quotientDenominator subtract x y=1 ∧
    zeroRepairedSign (sumNegative subtract x y) (quotientNumerator subtract x y)=false := by
  simpa only [hz,Rat.num_zero,Int.natAbs_zero,Rat.den_zero,sign,lt_self_iff_false,decide_false] using pipeline_fields subtract x y

theorem sub_self_fields (x : Rat) :
    quotientNumerator true x x=0 ∧ quotientDenominator true x x=1 ∧
    zeroRepairedSign (sumNegative true x x) (quotientNumerator true x x)=false :=
  cancellation_fields true x x (by simp [target])

theorem pipeline_output (subtract : Bool) (x y : Rat) :
    encode [.rational (target subtract x y)]=encodeNat 1 ++
      ([true,zeroRepairedSign (sumNegative subtract x y) (quotientNumerator subtract x y)] ++
        encodeNat (quotientNumerator subtract x y) ++ encodeNat (quotientDenominator subtract x y)) ++ [true] := by
  obtain ⟨hn,hd,hs⟩ := pipeline_fields subtract x y
  simp only [sign] at hs
  simp only [encode,List.length_singleton,List.flatMap_cons,List.flatMap_nil,List.append_nil,encodeDatum]
  rw [←hn,←hd,←hs]

/- Tight joint cross-product lengths, rather than a numerical exponential
bound, charge all real native calls to the four original canonical fields. -/
theorem left_bits (x y : Rat) : natBits (leftMagnitude x y)≤fieldWidth x y :=
  PA17TMRatArithmeticRatDivFields066.divMagnitude_bits x y
theorem right_bits (x y : Rat) : natBits (rightMagnitude x y)≤fieldWidth x y :=
  PA17TMRatArithmeticRatDivFields066.divDenominator_bits x y
theorem denominator_bits (x y : Rat) : natBits (commonDenominator x y)≤fieldWidth x y :=
  PA17TMRatArithmeticMulFields048.productDenominator_bits x y

theorem cross_pair_bits (x y : Rat) :
    natBits (leftMagnitude x y)+natBits (rightMagnitude x y)≤fieldWidth x y := by
  have hm := natBits_mul_le x.num.natAbs y.den
  have hn := natBits_mul_le x.den y.num.natAbs
  have he := PA17TMRatArithmeticMulFields048.inputBits_eq_fieldWidth x y
  change natBits (leftMagnitude x y)≤_ at hm
  change natBits (rightMagnitude x y)≤_ at hn
  unfold inputBits at he
  omega

theorem difference_bits (x y : Rat) :
    natBits (leftDifference x y)≤fieldWidth x y ∧ natBits (rightDifference x y)≤fieldWidth x y :=
  ⟨(natBits_mono (Nat.sub_le _ _)).trans (left_bits x y),
    (natBits_mono (Nat.sub_le _ _)).trans (right_bits x y)⟩

theorem sum_le_cross (subtract : Bool) (x y : Rat) :
    sumMagnitude subtract x y≤leftMagnitude x y+rightMagnitude x y := by
  cases h : sameSigns subtract x y
  · have hp := Nat.sub_le (leftMagnitude x y) (rightMagnitude x y)
    have hq := Nat.sub_le (rightMagnitude x y) (leftMagnitude x y)
    simp only [sumMagnitude,h,Bool.false_eq_true,ite_false,leftDifference,rightDifference]
    omega
  · simp only [sumMagnitude,h,ite_true,le_refl]

theorem sum_bits (subtract : Bool) (x y : Rat) : natBits (sumMagnitude subtract x y)≤fieldWidth x y :=
  ((natBits_mono (sum_le_cross subtract x y)).trans (natBits_add_le _ _)).trans (cross_pair_bits x y)

theorem normalizer_bits (subtract : Bool) (x y : Rat) : natBits (normalizer subtract x y)≤fieldWidth x y :=
  (natBits_mono (Nat.gcd_le_right (sumMagnitude subtract x y) (commonDenominator_pos x y))).trans (denominator_bits x y)

theorem quotient_bits (subtract : Bool) (x y : Rat) :
    natBits (quotientNumerator subtract x y)≤fieldWidth x y ∧
    natBits (quotientDenominator subtract x y)≤fieldWidth x y :=
  ⟨(natBits_mono (Nat.div_le_self _ _)).trans (sum_bits subtract x y),
    (natBits_mono (Nat.div_le_self _ _)).trans (denominator_bits x y)⟩

theorem all_field_bits (subtract : Bool) (x y : Rat) :
    natBits (leftMagnitude x y)≤fieldWidth x y ∧ natBits (rightMagnitude x y)≤fieldWidth x y ∧
    natBits (commonDenominator x y)≤fieldWidth x y ∧ natBits (leftDifference x y)≤fieldWidth x y ∧
    natBits (rightDifference x y)≤fieldWidth x y ∧ natBits (sumMagnitude subtract x y)≤fieldWidth x y ∧
    natBits (normalizer subtract x y)≤fieldWidth x y ∧ natBits (quotientNumerator subtract x y)≤fieldWidth x y ∧
    natBits (quotientDenominator subtract x y)≤fieldWidth x y :=
  ⟨left_bits x y,right_bits x y,denominator_bits x y,(difference_bits x y).1,(difference_bits x y).2,
    sum_bits subtract x y,normalizer_bits subtract x y,(quotient_bits subtract x y).1,(quotient_bits subtract x y).2⟩

theorem add_argument_bits (subtract : Bool) (x y : Rat) :
    natBits (addLeft subtract x y)≤fieldWidth x y ∧ natBits (addRight subtract x y)≤fieldWidth x y := by
  cases h : sameSigns subtract x y <;>
    simp only [addLeft,addRight,h,ite_true,Bool.false_eq_true,ite_false]
  · exact difference_bits x y
  · exact ⟨left_bits x y,right_bits x y⟩

theorem nine_scales (subtract : Bool) (x y : Rat) :
    scale x.num.natAbs y.den≤4*fieldWidth x y ∧ scale x.den y.num.natAbs≤4*fieldWidth x y ∧
    scale x.den y.den≤4*fieldWidth x y ∧
    scale (leftMagnitude x y) (rightMagnitude x y)≤4*fieldWidth x y ∧
    scale (rightMagnitude x y) (leftMagnitude x y)≤4*fieldWidth x y ∧
    scale (addLeft subtract x y) (addRight subtract x y)≤4*fieldWidth x y ∧
    scale (sumMagnitude subtract x y) (commonDenominator x y)≤4*fieldWidth x y ∧
    scale (sumMagnitude subtract x y) (normalizer subtract x y)≤4*fieldWidth x y ∧
    scale (commonDenominator x y) (normalizer subtract x y)≤4*fieldWidth x y := by
  obtain ⟨hnx,hny,hdx,hdy⟩ := PA17TMRatArithmeticMulFields048.original_field_bits x y
  have hw : 1≤fieldWidth x y := by have h:=PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y;omega
  have bound := PA17TMRatArithmeticMulFields048.scale_le_four_width (fieldWidth x y)
  obtain ⟨ha,hb⟩ := add_argument_bits subtract x y
  exact ⟨bound _ _ hw hnx hdy,bound _ _ hw hdx hny,bound _ _ hw hdx hdy,
    bound _ _ hw (left_bits x y) (right_bits x y),bound _ _ hw (right_bits x y) (left_bits x y),
    bound _ _ hw ha hb,bound _ _ hw (sum_bits subtract x y) (denominator_bits x y),
    bound _ _ hw (sum_bits subtract x y) (normalizer_bits subtract x y),
    bound _ _ hw (denominator_bits x y) (normalizer_bits subtract x y)⟩

theorem nine_windows (subtract : Bool) (x y : Rat) :
    window x.num.natAbs y.den≤allocationK*(fieldWidth x y)^2 ∧
    window x.den y.num.natAbs≤allocationK*(fieldWidth x y)^2 ∧
    window x.den y.den≤allocationK*(fieldWidth x y)^2 ∧
    window (leftMagnitude x y) (rightMagnitude x y)≤allocationK*(fieldWidth x y)^2 ∧
    window (rightMagnitude x y) (leftMagnitude x y)≤allocationK*(fieldWidth x y)^2 ∧
    window (addLeft subtract x y) (addRight subtract x y)≤allocationK*(fieldWidth x y)^2 ∧
    window (sumMagnitude subtract x y) (commonDenominator x y)≤allocationK*(fieldWidth x y)^2 ∧
    window (sumMagnitude subtract x y) (normalizer subtract x y)≤allocationK*(fieldWidth x y)^2 ∧
    window (commonDenominator x y) (normalizer subtract x y)≤allocationK*(fieldWidth x y)^2 := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := nine_scales subtract x y
  have hw : 1≤fieldWidth x y := by have h:=PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y;omega
  exact ⟨window_le_allocated _ _ _ hw h1,window_le_allocated _ _ _ hw h2,window_le_allocated _ _ _ hw h3,
    window_le_allocated _ _ _ hw h4,window_le_allocated _ _ _ hw h5,window_le_allocated _ _ _ hw h6,
    window_le_allocated _ _ _ hw h7,window_le_allocated _ _ _ hw h8,window_le_allocated _ _ _ hw h9⟩

theorem native_budget_le (x y : Rat) (a b : Nat) (hs : scale a b≤4*fieldWidth x y) :
    65536*(scale a b)^2≤PA17TMRatArithmeticRatDivFields066.nativeTimeCoefficient*PA17TMRatArithmeticRatDivFields066.inputPower x y ∧
    (encode [.rational x,.rational y]).length+131072*(scale a b)^2+1≤
      PA17TMRatArithmeticRatDivFields066.nativeSpaceCoefficient*PA17TMRatArithmeticRatDivFields066.inputPower x y :=
  PA17TMRatArithmeticRatDivFields066.native_budget_le x y a b hs

/- Only finite control interpretation. No assertion below executes a read,
mutates an actual TM state, or supplies a free phase transition. The caller
must really reach the row AFTER loading the original denominator fields. -/
def repairMemory (old : Fin 64) (negative : Bool) : Fin 64 :=
  ⟨old.val%4+8*((old.val/8)%4)+(if negative then 32 else 0),by
    have hlo := Nat.mod_lt old.val (by decide : 0<4)
    have hhi := Nat.mod_lt (old.val/8) (by decide : 0<4)
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩

theorem repairMemory_bits (old : Fin 64) (negative : Bool) :
    (repairMemory old negative).val.testBit 5=negative ∧
    (repairMemory old negative).val.testBit 2=false ∧
    (repairMemory old negative).val.testBit 0=old.val.testBit 0 ∧
    (repairMemory old negative).val.testBit 1=old.val.testBit 1 ∧
    (repairMemory old negative).val.testBit 3=old.val.testBit 3 ∧
    (repairMemory old negative).val.testBit 4=old.val.testBit 4 := by
  fin_cases old <;> cases negative <;> decide

def negativeControl (subtract : Bool) (old : Fin 64) (pZero : Bool) : Bool :=
  negativeChoice (old.val.testBit 5) (Bool.xor (old.val.testBit 2) subtract) pZero
def selectedMemory (subtract : Bool) (old : Fin 64) (pZero : Bool) : Fin 64 :=
  repairMemory old (negativeControl subtract old pZero)

theorem actual_negative_control (subtract : Bool) (x y : Rat) :
    negativeControl subtract (PA17TMRatArithmeticMulStart049.actualMemory x y)
      (decide (leftDifference x y=0))=sumNegative subtract x y := by
  have sx := (PA17TMRatArithmeticZeroCarry058.saved_sign_table (PA17TMRatArithmeticBookmark014.mNx x y) (sign x)).1
  have sy := (PA17TMRatArithmeticZeroCarry058.saved_sign_table (PA17TMRatArithmeticBookmark014.mNx x y) (sign x)).2.trans
    (PA17TMRatArithmeticBookmark014.observed_memory_bits x y).2.2.1
  change negativeChoice ((PA17TMRatArithmeticSignRead021.selectedMemory
      (PA17TMRatArithmeticBookmark014.mNx x y) (sign x)).val.testBit 5)
    (Bool.xor ((PA17TMRatArithmeticSignRead021.selectedMemory
      (PA17TMRatArithmeticBookmark014.mNx x y) (sign x)).val.testBit 2) subtract) _=_
  rw [sx,sy]
  rfl

theorem observed_output_sign (subtract : Bool) (x y : Rat) :
    PA17TMRatArithmeticZeroCarry058.repairedNegative
      (PA17TMRatArithmeticZeroCarry058.observedMemory
        (selectedMemory subtract (PA17TMRatArithmeticMulStart049.actualMemory x y)
          (decide (leftDifference x y=0))) (decide (quotientNumerator subtract x y=0)))=
      sign (target subtract x y) := by
  rw [PA17TMRatArithmeticZeroCarry058.observed_negative_table]
  let old := PA17TMRatArithmeticMulStart049.actualMemory x y
  let negative := negativeControl subtract old (decide (leftDifference x y=0))
  have hb := repairMemory_bits old negative
  change (if decide (quotientNumerator subtract x y=0) then false else
    Bool.xor ((repairMemory old negative).val.testBit 5) ((repairMemory old negative).val.testBit 2))=_
  rw [hb.1,hb.2.1]
  dsimp only [negative,old]
  rw [actual_negative_control]
  have h := (pipeline_fields subtract x y).2.2
  by_cases hz : quotientNumerator subtract x y=0 <;> simpa [zeroRepairedSign,hz] using h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSignedSumFields072
