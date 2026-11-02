module
public import Common.ROOT_TM_GCD_HalfCode_001
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDHalf001
open PaperProofs.Common.Native.RationalControllerComputation
local notation "Triple" => Pair
local notation "AVal" => PSTRTMBinaryAdd024.firstValue
local notation "BVal" => PSTRTMBinaryAdd024.secondValue

theorem control_specs (h s : Bool) : higherBit (carryControl h s)=h ∧ seenBit (carryControl h s)=s := by
  cases h <;> cases s <;> exact ⟨rfl,rfl⟩
theorem control_eta (r : Fin 4) : carryControl (higherBit r) (seenBit r)=r := by fin_cases r <;> rfl
theorem next_specs (r : Fin 4) (bit : Bool) : higherBit (nextCarry r bit)=bit ∧ seenBit (nextCarry r bit)=(seenBit r || higherBit r) :=
  control_specs _ _

theorem result_length (r : Fin 4) (triples : List Triple) : (resultReverse r triples).length=triples.length := by
  induction triples generalizing r with
  | nil => rfl
  | cons triple earlier ih => obtain ⟨a,b⟩ := triple; simp only [resultReverse,List.length_cons,ih]

theorem aFields_result (r : Fin 4) (triples : List Triple) :
    (resultReverse r triples).map (Prod.fst)=triples.map (Prod.fst) := by
  induction triples generalizing r with
  | nil => rfl
  | cons triple earlier ih => obtain ⟨a,b⟩ := triple; simp only [resultReverse,List.map_cons,ih]

theorem aValue_reverse_result (r : Fin 4) (triples : List Triple) : AVal (resultReverse r triples).reverse=AVal triples.reverse := by
  simp only [PSTRTMBinaryAdd024.firstValue,List.map_reverse,aFields_result]

theorem bValue_append_single (triples : List Triple) (a b : Bool) :
    BVal (triples++[(a,b)])=BVal triples+2^triples.length*b.toNat := by
  induction triples with
  | nil => cases b <;> rfl
  | cons triple earlier ih =>
    obtain ⟨aa,bb⟩ := triple
    change Nat.bit bb (BVal (earlier++[(a,b)]))=Nat.bit bb (BVal earlier)+2^(earlier.length+1)*b.toNat
    rw [ih]
    cases bb <;> simp only [Nat.bit,Bool.cond_false,Bool.cond_true,Nat.pow_succ] <;> nlinarith

/-- Exact fixed-width right-shift identity, including an arbitrary incoming
higherBit bit. The actual discarded LOW bit remains in the final carryControl. -/
theorem bValue_reverse_result (r : Fin 4) (triples : List Triple) :
    2*BVal (resultReverse r triples).reverse+(higherBit (finalControl r triples)).toNat =
      BVal triples.reverse+2^triples.length*(higherBit r).toNat := by
  induction triples generalizing r with
  | nil => simp [resultReverse,finalControl,PSTRTMBinaryAdd024.secondValue,PSTRTMIncrement009.valueDigits]
  | cons triple earlier ih =>
    obtain ⟨a,b⟩ := triple
    have ht := ih (nextCarry r b)
    rw [(next_specs r b).1] at ht
    simp only [resultReverse,finalControl,List.reverse_cons,bValue_append_single,List.length_reverse,result_length,List.length_cons]
    rw [Nat.pow_succ]
    nlinarith

def anyB (triples : List Triple) : Bool := triples.any (Prod.snd)
theorem anyB_reverse (triples : List Triple) : anyB triples.reverse=anyB triples := by
  simp only [anyB,List.any_reverse]

theorem seen_result (r : Fin 4) (triples : List Triple) :
    seenBit (finalControl r triples)= (seenBit r || anyB (resultReverse r triples)) := by
  induction triples generalizing r with
  | nil => simp [finalControl,resultReverse,anyB]
  | cons triple earlier ih =>
    obtain ⟨a,b⟩ := triple
    rw [finalControl,ih,(next_specs r b).2]
    simp only [resultReverse,anyB,List.any_cons,Bool.or_assoc]

theorem anyB_value (triples : List Triple) : anyB triples=decide (BVal triples≠0) := by
  induction triples with
  | nil => rfl
  | cons triple earlier ih =>
    obtain ⟨a,b⟩ := triple
    change (b || anyB earlier)=decide (Nat.bit b (BVal earlier)≠0)
    rw [ih]
    cases b <;> simp [Nat.bit]

theorem half_values (pairs : List Pair) :
    AVal (halfPairs pairs) = AVal pairs ∧ BVal (halfPairs pairs) = BVal pairs / 2 := by
  have ha := aValue_reverse_result (carryControl false false) pairs.reverse
  simp only [List.reverse_reverse] at ha
  have hb := bValue_reverse_result (carryControl false false) pairs.reverse
  rw [(control_specs false false).1] at hb
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, List.reverse_reverse] at hb
  have hl := Bool.toNat_le (higherBit (finalControl (carryControl false false) pairs.reverse))
  change AVal (halfPairs pairs) = AVal pairs at ha
  change 2 * BVal (halfPairs pairs) + (higherBit (finalControl (carryControl false false) pairs.reverse)).toNat = BVal pairs at hb
  exact ⟨ha, by omega⟩

theorem actual_low_bit (triples : List Triple) :
    higherBit (finalControl (carryControl false false) triples.reverse)=(BVal triples).testBit 0 := by
  have hb := bValue_reverse_result (carryControl false false) triples.reverse
  rw [(control_specs false false).1] at hb
  simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero,List.reverse_reverse] at hb
  have hl := Bool.toNat_le (higherBit (finalControl (carryControl false false) triples.reverse))
  have hm : BVal triples%2=(higherBit (finalControl (carryControl false false) triples.reverse)).toNat := by omega
  rw [Nat.testBit_zero,hm]
  cases higherBit (finalControl (carryControl false false) triples.reverse) <;> rfl

theorem actual_seen_bit (triples : List Triple) :
    seenBit (finalControl (carryControl false false) triples.reverse)=decide (BVal (halfPairs triples)≠0) := by
  have hs := seen_result (carryControl false false) triples.reverse
  rw [(control_specs false false).2,Bool.false_or] at hs
  rw [hs]
  change anyB (resultReverse (carryControl false false) triples.reverse)=
    decide (BVal (resultReverse (carryControl false false) triples.reverse).reverse≠0)
  rw [←anyB_reverse]
  exact anyB_value _

/-- This is the zero test used by the actual multiplication caller:
it comes from the OLD low bit and ACTUAL new nonzero bit, not a supplied
comparison/termination certificate. -/
theorem actual_zero_iff (triples : List Triple) :
    finalControl (carryControl false false) triples.reverse=0 ↔ BVal triples=0 := by
  have hb := bValue_reverse_result (carryControl false false) triples.reverse
  rw [(control_specs false false).1] at hb
  simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero,List.reverse_reverse] at hb
  have hl := Bool.toNat_le (higherBit (finalControl (carryControl false false) triples.reverse))
  constructor
  · intro hz
    have hzero : higherBit (finalControl (carryControl false false) triples.reverse)=false := by rw [hz]; rfl
    have hs : seenBit (finalControl (carryControl false false) triples.reverse)=false := by rw [hz]; rfl
    rw [actual_seen_bit] at hs
    have hv : BVal (halfPairs triples)=0 := by simpa using hs
    change 2*BVal (halfPairs triples)+(higherBit (finalControl (carryControl false false) triples.reverse)).toNat=BVal triples at hb
    rw [hzero] at hb
    simp only [Bool.toNat_false] at hb
    omega
  · intro hz
    change 2*BVal (halfPairs triples)+(higherBit (finalControl (carryControl false false) triples.reverse)).toNat=BVal triples at hb
    have hv : BVal (halfPairs triples)=0 := by omega
    have hlow : (higherBit (finalControl (carryControl false false) triples.reverse)).toNat=0 := by omega
    have hfalse := Bool.toNat_eq_zero.mp hlow
    rw [←control_eta (finalControl (carryControl false false) triples.reverse),hfalse,actual_seen_bit]
    have hc0 : carryControl false false=(0 : Fin 4) := rfl
    simpa only [hv,ne_self_iff_false,decide_false] using hc0

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDHalf001
