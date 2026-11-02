module
public import Structure.PA17_TM_RatArithmetic_CachedOuter_043e
public import Structure.PA17_TM_RatArithmetic_MulFields_048c
public import Structure.PA17_TM_RatArithmetic_WideCache_045b

/-! Only costs of the already-frozen real043 producer are bounded here.
No allocator, scanner, counter, native call, or new TM is defined. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocationBounds056
open Turing PA17TMRatArithmeticCachedOuter043 PA17TMRatArithmeticCachedPass036
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticMulFields048 PA17TMRatArithmeticWideCache045
open PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002

def timeCoefficient (k : Nat) : Nat := 256*(k+256)
def allocationCoefficient : Nat := 1024*(allocationK+256)

theorem allocationCoefficient_pos : 0<allocationCoefficient := by
  unfold allocationCoefficient
  positivity

private theorem coefficient_comparison (k : Nat) :
    timeCoefficient k≤1024*(k+256) ∧ 2*timeCoefficient k+1≤1024*(k+256) := by
  unfold timeCoefficient
  constructor
  · omega
  · omega

private theorem fee_collected (j k : Nat) (records : List RecordSpec) (w : Nat) :
    outerFee j k records w=
      (2*totalGap records+4*totalWidth records+21*j)*(w*(w+1)+1)+
        (2*k*w^4+(4*k+4)*w^3+(6*k+86)*w^2+(4*k+212)*w+183) := by
  unfold outerFee prepareFee refillFee loopFee
  ring

private def feePolynomial (k w : Nat) : Nat :=
  22*k*w^4+(24*k+24)*w^3+(26*k+190)*w^2+(4*k+316)*w+267

/-- Coarse bounds allow five old records; the native-call code indices
are the fixed values0..4. Every G/V/j traversal term is retained. -/
private theorem fee_le_polynomial (j k : Nat) (records : List RecordSpec) (w : Nat)
    (hj : j≤4) (hg : totalGap records≤10*k*w^2) (hv : totalWidth records≤5*w) :
    outerFee j k records w≤feePolynomial k w := by
  have bank : 2*totalGap records+4*totalWidth records+21*j≤20*k*w^2+20*w+84 := by
    calc
      _ ≤ 2*(10*k*w^2)+4*(5*w)+21*4 :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 hg) (Nat.mul_le_mul_left 4 hv))
          (Nat.mul_le_mul_left 21 hj)
      _ = _ := by ring
  have scaled := Nat.mul_le_mul_right (w*(w+1)+1) bank
  calc
    _ = (2*totalGap records+4*totalWidth records+21*j)*(w*(w+1)+1)+
        (2*k*w^4+(4*k+4)*w^3+(6*k+86)*w^2+(4*k+212)*w+183) := fee_collected j k records w
    _ ≤ (20*k*w^2+20*w+84)*(w*(w+1)+1)+
        (2*k*w^4+(4*k+4)*w^3+(6*k+86)*w^2+(4*k+212)*w+183) := Nat.add_le_add_right scaled _
    _ = feePolynomial k w := by unfold feePolynomial;ring

private theorem polynomial_le_power (k w n : Nat) (hw : w≤n) (hn : 1≤n) :
    feePolynomial k w≤timeCoefficient k*n^4 := by
  have h4 := Nat.pow_le_pow_left hw 4
  have h3 : w^3≤n^4 := (Nat.pow_le_pow_left hw 3).trans
    (Nat.pow_le_pow_right hn (by decide : (3 : Nat) ≤ 4))
  have h2 : w^2≤n^4 := (Nat.pow_le_pow_left hw 2).trans
    (Nat.pow_le_pow_right hn (by decide : (2 : Nat) ≤ 4))
  have h1 : w≤n^4 := hw.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right hn (by decide : (1 : Nat) ≤ 4))
  have h0 : 1≤n^4 := by simpa only [one_pow] using Nat.pow_le_pow_left hn 4
  have terms := Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left (22*k) h4) (Nat.mul_le_mul_left (24*k+24) h3))
        (Nat.mul_le_mul_left (26*k+190) h2))
      (Nat.mul_le_mul_left (4*k+316) h1))
    (Nat.mul_le_mul_left 267 h0)
  calc
    _ = 22*k*w^4+(24*k+24)*w^3+(26*k+190)*w^2+(4*k+316)*w+267*1 := by
      unfold feePolynomial
      ring
    _ ≤ 22*k*n^4+(24*k+24)*n^4+(26*k+190)*n^4+(4*k+316)*n^4+267*n^4 := terms
    _ = (76*k+797)*n^4 := by ring
    _ ≤ timeCoefficient k*n^4 := Nat.mul_le_mul_right _ (by unfold timeCoefficient;omega)

/-- Frozen048 sums the TRUE sizes of previously produced cache records.
The hypotheses are internal producer invariants, never original inputs. -/
theorem cache_totals_le (j : Nat) (records : List RecordSpec) (hrecords : records.length=j)
    (hj : j≤4) (x y : Rat)
    (hg : ∀ r∈records,r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈records,r.digits.length≤fieldWidth x y) :
    totalGap records≤10*allocationK*(fieldWidth x y)^2 ∧ totalWidth records≤5*fieldWidth x y := by
  obtain ⟨gap,width⟩ := fixed_bank_bounds j allocationK records hrecords x y hg hv
  have hj5 : j≤5 := by omega
  constructor
  · calc
      _ ≤ 2*j*allocationK*(fieldWidth x y)^2 := gap
      _ = j*(2*allocationK*(fieldWidth x y)^2) := by ring
      _ ≤ 5*(2*allocationK*(fieldWidth x y)^2) := Nat.mul_le_mul_right _ hj5
      _ = 10*allocationK*(fieldWidth x y)^2 := by ring
  · exact width.trans (Nat.mul_le_mul_right _ hj5)

/-- A fixed positive coefficient bounds043's exact whole outer fee by
ORIGINAL input length, without any numeric qualification on x or y. -/
theorem original_outerFee_le (j : Nat) (records : List RecordSpec) (hrecords : records.length=j)
    (hj : j≤4) (x y : Rat)
    (hg : ∀ r∈records,r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈records,r.digits.length≤fieldWidth x y) :
    outerFee j allocationK records (fieldWidth x y)≤
      timeCoefficient allocationK*((encode [.rational x,.rational y]).length+1)^4 := by
  obtain ⟨gap,width⟩ := cache_totals_le j records hrecords hj x y hg hv
  have fee := fee_le_polynomial j allocationK records (fieldWidth x y) hj gap width
  have input := original_width_le_input x y
  exact fee.trans (polynomial_le_power allocationK (fieldWidth x y)
    ((encode [.rational x,.rational y]).length+1) (by omega) (by omega))

/-- This consumes the SAME actual frozen043 trace. Its fresh K*W^2 gap
is really produced, never assumed as a target width or extra input. The
observed opaque carry is retained in all rows, including p127. The frozen
trace length is independent of the number of compiled control rows. -/
theorem actual_allocation_contract (p j : Nat) (memory : Fin (p+1))
    (records : List RecordSpec) (hrecords : records.length=j) (hj : j≤4) (x y : Rat)
    (hg : ∀ r∈records,r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈records,r.digits.length≤fieldWidth x y) :
    ∃ trace, PSTRTMSeq005.RunsFrom (carryMachine p j allocationK)
      (carryEntry p j allocationK memory (Tape.mk₂ [false]
        (prefixRight (sign x) (originalBank x y (bankTail records []))))) trace
      (carryFinal p j allocationK memory (Tape.mk₂ [false] (prefixRight (sign x)
        (originalBank x y (cachedTail records (allocationK*(fieldWidth x y)^2)))))) ∧
      trace.length≤allocationCoefficient*((encode [.rational x,.rational y]).length+1)^4 ∧
      ∀ prefixLength, visitedSpace (carryMachine p j allocationK) (encode [.rational x,.rational y]).length
        (trace.take prefixLength)≤allocationCoefficient*((encode [.rational x,.rational y]).length+1)^4 := by
  obtain ⟨trace,hr,ht,hs⟩ := original_carry_contract p j allocationK memory records hrecords x y
  let i := (encode [.rational x,.rational y]).length
  have hf : outerFee j allocationK records (fieldWidth x y)≤timeCoefficient allocationK*(i+1)^4 :=
    original_outerFee_le j records hrecords hj x y hg hv
  have hi : i+1≤(i+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le i)) (by decide : (1 : Nat) ≤ 4)
  have hc : timeCoefficient allocationK≤allocationCoefficient := (coefficient_comparison allocationK).1
  refine ⟨trace,hr,(ht.trans hf).trans (Nat.mul_le_mul_right _ hc),?_⟩
  intro prefixLength
  have hspace : visitedSpace (carryMachine p j allocationK) i (trace.take prefixLength)≤
      i+2*outerFee j allocationK records (fieldWidth x y)+1 := hs prefixLength
  change visitedSpace (carryMachine p j allocationK) i (trace.take prefixLength)≤allocationCoefficient*(i+1)^4
  calc
    _ ≤ i+2*outerFee j allocationK records (fieldWidth x y)+1 := hspace
    _ ≤ i+2*(timeCoefficient allocationK*(i+1)^4)+1 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hf) i) 1
    _ = (i+1)+2*(timeCoefficient allocationK*(i+1)^4) := by ac_rfl
    _ ≤ (i+1)^4+2*(timeCoefficient allocationK*(i+1)^4) := Nat.add_le_add_right hi _
    _ = (2*timeCoefficient allocationK+1)*(i+1)^4 := by ring
    _ ≤ allocationCoefficient*(i+1)^4 := Nat.mul_le_mul_right _ (coefficient_comparison allocationK).2

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocationBounds056
