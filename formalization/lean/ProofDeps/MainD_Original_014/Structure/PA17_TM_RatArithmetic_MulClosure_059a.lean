module
public import Structure.PA17_TM_RatArithmetic_AllocationBounds_056a
public import Structure.PA17_TM_RatArithmetic_NativeTail_055c
public import Structure.PA17_TM_RatArithmetic_ZeroCarry_058e
public import Structure.PA17_TM_RatArithmetic_SignDispatch_053b

/-! Concrete cost glue for the actual five-cache multiplication chain.
The fifth allocation uses TOTAL count5;056 correctly covers only totals<=4.
No new allocator, native program, observer or output implementation is defined. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulClosure059

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedOuter043
open PA17TMRatArithmeticCachedPass036 PA17TMRatArithmeticMulFields048
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticAllocationBounds056

def nativeCoefficient : Nat := 2097152*(allocationK+256)

private theorem collected_polynomial (a b c d e w n : Nat) (hw : w≤n) (hn : 1≤n) :
    a*w^4+b*w^3+c*w^2+d*w+e≤(a+b+c+d+e)*n^4 := by
  have h4 := Nat.pow_le_pow_left hw 4
  have h3 := (Nat.pow_le_pow_left hw 3).trans
    (Nat.pow_le_pow_right hn (by decide : (3 : Nat) ≤ 4))
  have h2 := (Nat.pow_le_pow_left hw 2).trans
    (Nat.pow_le_pow_right hn (by decide : (2 : Nat) ≤ 4))
  have h1 : w≤n^4 := hw.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right hn (by decide : (1 : Nat) ≤ 4))
  have h0 : 1≤n^4 := by simpa only [one_pow] using Nat.pow_le_pow_left hn 4
  have terms := Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left a h4) (Nat.mul_le_mul_left b h3))
        (Nat.mul_le_mul_left c h2)) (Nat.mul_le_mul_left d h1))
    (Nat.mul_le_mul_left e h0)
  calc
    _ = a*w^4+b*w^3+c*w^2+d*w+e*1 := by ring
    _ ≤ a*n^4+b*n^4+c*n^4+d*n^4+e*n^4 := terms
    _ = _ := by ring

private theorem quadratic_budget (a b c w n : Nat) (hw : w≤n) (hn : 1≤n) :
    a*w^2+b*w+c≤(a+b+c)*n^4 := by
  simpa only [Nat.zero_mul,Nat.zero_add] using collected_polynomial 0 0 a b c w n hw hn

private theorem fifth_fee_collected (k : Nat) (records : List RecordSpec) (w : Nat) :
    outerFee 5 k records w=
      (2*totalGap records+4*totalWidth records+105)*(w*(w+1)+1)+
        (2*k*w^4+(4*k+4)*w^3+(6*k+86)*w^2+(4*k+212)*w+183) := by
  unfold outerFee prepareFee refillFee loopFee
  ring

/-- Total5 is the real output-workspace allocation after M,D,G,U,V exist. -/
theorem fifth_fee_le (k : Nat) (records : List RecordSpec) (w n : Nat)
    (hg : totalGap records≤10*k*w^2) (hv : totalWidth records≤5*w)
    (hw : w≤n) (hn : 1≤n) :
    outerFee 5 k records w≤timeCoefficient k*n^4 := by
  have bank : 2*totalGap records+4*totalWidth records+105≤20*k*w^2+20*w+105 := by
    nlinarith only [hg,hv]
  have scaled := Nat.mul_le_mul_right (w*(w+1)+1) bank
  have fee : outerFee 5 k records w≤
      22*k*w^4+(24*k+24)*w^3+(26*k+211)*w^2+(4*k+337)*w+288 := by
    calc
      _ = _ := fifth_fee_collected k records w
      _ ≤ (20*k*w^2+20*w+105)*(w*(w+1)+1)+
          (2*k*w^4+(4*k+4)*w^3+(6*k+86)*w^2+(4*k+212)*w+183) := Nat.add_le_add_right scaled _
      _ = _ := by ring
  have polynomial := collected_polynomial (22*k) (24*k+24) (26*k+211) (4*k+337) 288 w n hw hn
  have coefficient : 22*k+(24*k+24)+(26*k+211)+(4*k+337)+288≤timeCoefficient k := by
    unfold timeCoefficient
    omega
  exact fee.trans (polynomial.trans (Nat.mul_le_mul_right _ coefficient))

theorem original_fifth_fee_le (records : List RecordSpec) (hrecords : records.length=5) (x y : Rat)
    (hg : ∀ r∈records,r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈records,r.digits.length≤fieldWidth x y) :
    outerFee 5 allocationK records (fieldWidth x y)≤
      timeCoefficient allocationK*((encode [.rational x,.rational y]).length+1)^4 := by
  obtain ⟨gap,width⟩ := fixed_bank_bounds 5 allocationK records hrecords x y hg hv
  have actualGap : totalGap records≤10*allocationK*(fieldWidth x y)^2 := by
    nlinarith only [gap]
  have input := original_width_le_input x y
  exact fifth_fee_le allocationK records (fieldWidth x y)
    ((encode [.rational x,.rational y]).length+1) actualGap width (by omega) (by omega)

private theorem input_fourth (i : Nat) : i+1≤(i+1)^4 := by
  simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le i))
    (by decide : (1 : Nat) ≤ 4)

private theorem fifth_coefficients : timeCoefficient allocationK≤allocationCoefficient ∧
    2*timeCoefficient allocationK+1≤allocationCoefficient := by
  constructor <;> decide

/-- The actual frozen043 execution produces the fresh gap with all128
rows installed before values. No input eligibility or assumed workzone. -/
theorem actual_fifth_allocation (p : Nat) (memory : Fin (p+1))
    (records : List RecordSpec) (hrecords : records.length=5) (x y : Rat)
    (hg : ∀ r∈records,r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈records,r.digits.length≤fieldWidth x y) :
    ∃ trace, PSTRTMSeq005.RunsFrom (carryMachine p 5 allocationK)
      (carryEntry p 5 allocationK memory (Tape.mk₂ [false]
        (prefixRight (sign x) (originalBank x y (bankTail records []))))) trace
      (carryFinal p 5 allocationK memory (Tape.mk₂ [false] (prefixRight (sign x)
        (originalBank x y (cachedTail records (allocationK*(fieldWidth x y)^2)))))) ∧
      trace.length≤allocationCoefficient*((encode [.rational x,.rational y]).length+1)^4 ∧
      ∀ prefixLength, visitedSpace (carryMachine p 5 allocationK) (encode [.rational x,.rational y]).length
        (trace.take prefixLength)≤allocationCoefficient*((encode [.rational x,.rational y]).length+1)^4 := by
  let i := (encode [.rational x,.rational y]).length
  have fee : outerFee 5 allocationK records (fieldWidth x y)≤timeCoefficient allocationK*(i+1)^4 :=
    original_fifth_fee_le records hrecords x y hg hv
  have input := input_fourth i
  obtain ⟨trace,run,time,space⟩ := original_carry_contract p 5 allocationK memory records hrecords x y
  refine ⟨trace,run,(time.trans fee).trans (Nat.mul_le_mul_right _ fifth_coefficients.1),?_⟩
  intro prefixLength
  have actualSpace : visitedSpace (carryMachine p 5 allocationK) i (trace.take prefixLength)≤
      i+2*outerFee 5 allocationK records (fieldWidth x y)+1 := space prefixLength
  change visitedSpace (carryMachine p 5 allocationK) i (trace.take prefixLength)≤allocationCoefficient*(i+1)^4
  calc
    _ ≤ i+2*outerFee 5 allocationK records (fieldWidth x y)+1 := actualSpace
    _ ≤ i+2*(timeCoefficient allocationK*(i+1)^4)+1 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 fee) i) 1
    _ = (i+1)+2*(timeCoefficient allocationK*(i+1)^4) := by ac_rfl
    _ ≤ (i+1)^4+2*(timeCoefficient allocationK*(i+1)^4) := Nat.add_le_add_right input _
    _ = (2*timeCoefficient allocationK+1)*(i+1)^4 := by ring
    _ ≤ allocationCoefficient*(i+1)^4 := Nat.mul_le_mul_right _ fifth_coefficients.2

theorem native_tail_fee_le (j : Nat) (hj : j≤3) (first : RecordSpec) (later : List RecordSpec)
    (nx dx ny dy : List Bool) (newGap a b value w n : Nat)
    (hg : totalGap (first::later)≤10*allocationK*w^2)
    (hv : totalWidth (first::later)≤5*w) (hnew : newGap≤2*allocationK*w^2)
    (hs : PA17TMRatArithmeticNativeCache030.scale a b≤4*w) (hout : natBits value≤w)
    (hsource : bankWidth nx dx ny dy≤w) (hw : w≤n) (hn : 1≤n) :
    PA17TMRatArithmeticNativeTail055.tailFee j first later nx dx ny dy newGap a b value≤
      nativeCoefficient*n^4 := by
  have square := Nat.pow_le_pow_left hs 2
  have fee : PA17TMRatArithmeticNativeTail055.tailFee j first later nx dx ny dy newGap a b value≤
      (1048576+12*allocationK)*w^2+14*w+97 := by
    unfold PA17TMRatArithmeticNativeTail055.tailFee
    nlinarith only [hg,hv,hnew,square,hout,hsource,hj]
  have polynomial := quadratic_budget (1048576+12*allocationK) 14 97 w n hw hn
  have coefficient : (1048576+12*allocationK)+14+97≤nativeCoefficient := by decide
  exact fee.trans (polynomial.trans (Nat.mul_le_mul_right _ coefficient))

theorem native_v_fee_le (a b w n : Nat)
    (hs : PA17TMRatArithmeticNativeCache030.scale a b≤4*w) (hw : w≤n) (hn : 1≤n) :
    65536*(PA17TMRatArithmeticNativeCache030.scale a b)^2≤nativeCoefficient*n^4 := by
  have square := Nat.pow_le_pow_left hs 2
  have cost : 65536*(PA17TMRatArithmeticNativeCache030.scale a b)^2≤1048576*w^2 := by nlinarith only [square]
  have polynomial := quadratic_budget 1048576 0 0 w n hw hn
  have h : 1048576≤nativeCoefficient := by decide
  exact cost.trans (by
    have bound : 1048576*w^2≤1048576*n^4 := by simpa only [Nat.zero_mul,Nat.add_zero] using polynomial
    exact bound.trans (Nat.mul_le_mul_right _ h))

theorem observe_fee_le (first : RecordSpec) (before following : List RecordSpec)
    (nx dx ny dy : List Bool) (sourceGap u w n : Nat)
    (hg : totalGap (first::PA17TMRatArithmeticZeroCarry058.observedRecords before following sourceGap u)≤10*allocationK*w^2)
    (hv : totalWidth (first::PA17TMRatArithmeticZeroCarry058.observedRecords before following sourceGap u)≤5*w)
    (hgf : totalGap following≤2*allocationK*w^2) (hvf : totalWidth following≤w)
    (hu : natBits u≤w) (hsource : bankWidth nx dx ny dy≤w) (hw : w≤n) (hn : 1≤n) :
    PA17TMRatArithmeticZeroCarry058.observeFee 1 4 first before following nx dx ny dy sourceGap u≤
      allocationCoefficient*n^4 := by
  have fee : PA17TMRatArithmeticZeroCarry058.observeFee 1 4 first before following nx dx ny dy sourceGap u≤
      14*allocationK*w^2+20*w+139 := by
    unfold PA17TMRatArithmeticZeroCarry058.observeFee PA17TMRatArithmeticZeroCarry058.readFee
      PA17TMRatArithmeticZeroCarry058.returnFee
    nlinarith only [hg,hv,hgf,hvf,hu,hsource]
  have polynomial := quadratic_budget (14*allocationK) 20 139 w n hw hn
  have coefficient : 14*allocationK+20+139≤allocationCoefficient := by decide
  exact fee.trans (polynomial.trans (Nat.mul_le_mul_right _ coefficient))

theorem output_fee_le (first : RecordSpec) (later : List RecordSpec)
    (nx dxTail ny dyTail : List Bool) (gap u v w n : Nat)
    (hg : totalGap (first::later)≤10*allocationK*w^2) (hv : totalWidth (first::later)≤5*w)
    (hsource : PA17TMRatArithmeticFinalClean039.sourceWidth nx dxTail ny dyTail≤w)
    (hgap : gap≤allocationK*w^2)
    (hu : (PA17TMRatArithmeticPairEncode017.payload u).length≤w)
    (hden : (PA17TMRatArithmeticPairEncode017.payload v).length≤w) (hw : w≤n) (hn : 1≤n) :
    1+PA17TMRatArithmeticOutputFinish044.outputFee 4 first later nx dxTail ny dyTail gap u v≤
      allocationCoefficient*n^4 := by
  have size : PA17TMRatArithmeticOutputFinish044.pairSize u v≤2*w+1 := by
    unfold PA17TMRatArithmeticOutputFinish044.pairSize
    omega
  have square := Nat.pow_le_pow_left size 2
  have fee : 1+PA17TMRatArithmeticOutputFinish044.outputFee 4 first later nx dxTail ny dyTail gap u v≤
      (42*allocationK+256)*w^2+336*w+445 := by
    unfold PA17TMRatArithmeticOutputFinish044.outputFee PA17TMRatArithmeticOutputFinish044.tailFee
      PA17TMRatArithmeticFinalClean039.cacheGap PA17TMRatArithmeticFinalClean039.cacheWidth
    nlinarith only [hg,hv,hsource,hgap,square]
  have polynomial := quadratic_budget (42*allocationK+256) 336 445 w n hw hn
  have coefficient : (42*allocationK+256)+336+445≤allocationCoefficient := by decide
  exact fee.trans (polynomial.trans (Nat.mul_le_mul_right _ coefficient))

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulClosure059
