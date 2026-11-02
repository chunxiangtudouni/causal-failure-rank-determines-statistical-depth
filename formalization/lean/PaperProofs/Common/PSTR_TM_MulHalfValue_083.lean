module
public import PaperProofs.Common.PSTR_TM_MulHalfCode_082
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulHalfValue083
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulHalfCode082
local notation "Triple" => PSTRTMMulPassCode079.Triple
local notation "CVal" => PSTRTMMulPassCode079.cValue
local notation "AVal" => PSTRTMMulPassCode079.aValue
local notation "BVal" => PSTRTMMulPassCode079.bValue

theorem control_specs (h s : Bool) : higher (control h s)=h ∧ seen (control h s)=s := by
  cases h <;> cases s <;> exact ⟨rfl,rfl⟩
theorem control_eta (r : Fin 4) : control (higher r) (seen r)=r := by fin_cases r <;> rfl
theorem next_specs (r : Fin 4) (bit : Bool) : higher (nextControl r bit)=bit ∧ seen (nextControl r bit)=(seen r || higher r) :=
  control_specs _ _

theorem result_length (r : Fin 4) (triples : List Triple) : (resultReverse r triples).length=triples.length := by
  induction triples generalizing r with
  | nil => rfl
  | cons triple earlier ih => obtain ⟨c,a,b⟩ := triple; simp only [resultReverse,List.length_cons,ih]

theorem cFields_result (r : Fin 4) (triples : List Triple) :
    (resultReverse r triples).map (fun (c,_,_) => c)=triples.map (fun (c,_,_) => c) := by
  induction triples generalizing r with
  | nil => rfl
  | cons triple earlier ih => obtain ⟨c,a,b⟩ := triple; simp only [resultReverse,List.map_cons,ih]
theorem aFields_result (r : Fin 4) (triples : List Triple) :
    (resultReverse r triples).map (fun (_,a,_) => a)=triples.map (fun (_,a,_) => a) := by
  induction triples generalizing r with
  | nil => rfl
  | cons triple earlier ih => obtain ⟨c,a,b⟩ := triple; simp only [resultReverse,List.map_cons,ih]

theorem cValue_reverse_result (r : Fin 4) (triples : List Triple) : CVal (resultReverse r triples).reverse=CVal triples.reverse := by
  simp only [PSTRTMMulPassCode079.cValue,List.map_reverse,cFields_result]
theorem aValue_reverse_result (r : Fin 4) (triples : List Triple) : AVal (resultReverse r triples).reverse=AVal triples.reverse := by
  simp only [PSTRTMMulPassCode079.aValue,List.map_reverse,aFields_result]

theorem bValue_append_single (triples : List Triple) (c a b : Bool) :
    BVal (triples++[(c,a,b)])=BVal triples+2^triples.length*b.toNat := by
  induction triples with
  | nil => cases b <;> rfl
  | cons triple earlier ih =>
    obtain ⟨cc,aa,bb⟩ := triple
    change Nat.bit bb (BVal (earlier++[(c,a,b)]))=Nat.bit bb (BVal earlier)+2^(earlier.length+1)*b.toNat
    rw [ih]
    cases bb <;> simp only [Nat.bit,Bool.cond_false,Bool.cond_true,Nat.pow_succ] <;> nlinarith

/-- Exact fixed-width right-shift identity, including an arbitrary incoming
higher bit. The actual discarded LOW bit remains in the final control. -/
theorem bValue_reverse_result (r : Fin 4) (triples : List Triple) :
    2*BVal (resultReverse r triples).reverse+(higher (finalControl r triples)).toNat =
      BVal triples.reverse+2^triples.length*(higher r).toNat := by
  induction triples generalizing r with
  | nil => simp [resultReverse,finalControl,PSTRTMMulPassCode079.bValue,PSTRTMIncrement009.valueDigits]
  | cons triple earlier ih =>
    obtain ⟨c,a,b⟩ := triple
    have ht := ih (nextControl r b)
    rw [(next_specs r b).1] at ht
    simp only [resultReverse,finalControl,List.reverse_cons,bValue_append_single,List.length_reverse,result_length,List.length_cons]
    rw [Nat.pow_succ]
    nlinarith

def anyB (triples : List Triple) : Bool := triples.any (fun (_,_,b) => b)
theorem anyB_reverse (triples : List Triple) : anyB triples.reverse=anyB triples := by
  simp only [anyB,List.any_reverse]

theorem seen_result (r : Fin 4) (triples : List Triple) :
    seen (finalControl r triples)= (seen r || anyB (resultReverse r triples)) := by
  induction triples generalizing r with
  | nil => simp [finalControl,resultReverse,anyB]
  | cons triple earlier ih =>
    obtain ⟨c,a,b⟩ := triple
    rw [finalControl,ih,(next_specs r b).2]
    simp only [resultReverse,anyB,List.any_cons,Bool.or_assoc]

theorem anyB_value (triples : List Triple) : anyB triples=decide (BVal triples≠0) := by
  induction triples with
  | nil => rfl
  | cons triple earlier ih =>
    obtain ⟨c,a,b⟩ := triple
    change (b || anyB earlier)=decide (Nat.bit b (BVal earlier)≠0)
    rw [ih]
    cases b <;> simp [Nat.bit]

theorem half_values (triples : List Triple) :
    CVal (halfTriples triples)=CVal triples ∧ AVal (halfTriples triples)=AVal triples ∧
      BVal (halfTriples triples)=BVal triples/2 := by
  have hc := cValue_reverse_result (control false false) triples.reverse
  have ha := aValue_reverse_result (control false false) triples.reverse
  simp only [List.reverse_reverse] at hc ha
  have hb := bValue_reverse_result (control false false) triples.reverse
  rw [(control_specs false false).1] at hb
  simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero,List.reverse_reverse] at hb
  have hl := Bool.toNat_le (higher (finalControl (control false false) triples.reverse))
  change CVal (halfTriples triples)=CVal triples at hc
  change AVal (halfTriples triples)=AVal triples at ha
  change 2*BVal (halfTriples triples)+(higher (finalControl (control false false) triples.reverse)).toNat=BVal triples at hb
  exact ⟨hc,ha,by omega⟩

theorem actual_low_bit (triples : List Triple) :
    higher (finalControl (control false false) triples.reverse)=(BVal triples).testBit 0 := by
  have hb := bValue_reverse_result (control false false) triples.reverse
  rw [(control_specs false false).1] at hb
  simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero,List.reverse_reverse] at hb
  have hl := Bool.toNat_le (higher (finalControl (control false false) triples.reverse))
  have hm : BVal triples%2=(higher (finalControl (control false false) triples.reverse)).toNat := by omega
  rw [Nat.testBit_zero,hm]
  cases higher (finalControl (control false false) triples.reverse) <;> rfl

theorem actual_seen_bit (triples : List Triple) :
    seen (finalControl (control false false) triples.reverse)=decide (BVal (halfTriples triples)≠0) := by
  have hs := seen_result (control false false) triples.reverse
  rw [(control_specs false false).2,Bool.false_or] at hs
  rw [hs]
  change anyB (resultReverse (control false false) triples.reverse)=
    decide (BVal (resultReverse (control false false) triples.reverse).reverse≠0)
  rw [←anyB_reverse]
  exact anyB_value _

/-- This is the zero test used by the actual multiplication caller:
it comes from the OLD low bit and ACTUAL new nonzero bit, not a supplied
comparison/termination certificate. -/
theorem actual_zero_iff (triples : List Triple) :
    finalControl (control false false) triples.reverse=0 ↔ BVal triples=0 := by
  have hb := bValue_reverse_result (control false false) triples.reverse
  rw [(control_specs false false).1] at hb
  simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero,List.reverse_reverse] at hb
  have hl := Bool.toNat_le (higher (finalControl (control false false) triples.reverse))
  constructor
  · intro hz
    have hzero : higher (finalControl (control false false) triples.reverse)=false := by simp [hz,higher]
    have hs : seen (finalControl (control false false) triples.reverse)=false := by simp [hz,seen]
    rw [actual_seen_bit] at hs
    have hv : BVal (halfTriples triples)=0 := by simpa using hs
    change 2*BVal (halfTriples triples)+(higher (finalControl (control false false) triples.reverse)).toNat=BVal triples at hb
    rw [hzero] at hb
    simp only [Bool.toNat_false] at hb
    omega
  · intro hz
    change 2*BVal (halfTriples triples)+(higher (finalControl (control false false) triples.reverse)).toNat=BVal triples at hb
    have hv : BVal (halfTriples triples)=0 := by omega
    have hlow : (higher (finalControl (control false false) triples.reverse)).toNat=0 := by omega
    have hfalse := Bool.toNat_eq_zero.mp hlow
    rw [←control_eta (finalControl (control false false) triples.reverse),hfalse,actual_seen_bit]
    have hc0 : control false false=(0 : Fin 4) := rfl
    simpa only [hv,ne_self_iff_false,decide_false] using hc0

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulHalfValue083
