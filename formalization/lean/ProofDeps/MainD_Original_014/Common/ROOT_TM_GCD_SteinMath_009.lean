module
public import Common.ROOT_TM_GCD_HalfValue_002
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.GCD.Basic

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDSteinMath009

/-- Zero-aware bit size. The original encoder gives zero one bit, so its
raw length cannot serve as the strict ranking function at the final step. -/
def rank (a b : Nat) : Nat := a.size+b.size

theorem size_half (a : Nat) (ha : a≠0) : (a/2).size+1=a.size := by
  have hbit : Nat.bit (decide (a%2=1)) (a/2)=a := by
    have hm := Nat.mod_lt a (by decide : 0<2)
    by_cases h : a%2=1
    · simp only [h,decide_true,Nat.bit,Bool.cond_true]
      omega
    · simp only [h,decide_false,Nat.bit,Bool.cond_false]
      omega
  have hz : Nat.bit (decide (a%2=1)) (a/2)≠0 := by rwa [hbit]
  have hs := Nat.size_bit hz
  rw [hbit] at hs
  omega

theorem half_size_lt (a : Nat) (ha : a≠0) : (a/2).size<a.size := by
  have h:=size_half a ha
  omega

theorem subtraction_half_size_lt (a b : Nat) (ha : a≠0) :
    ((a-b)/2).size<a.size := by
  have h : (a-b)/2≤a/2 := Nat.div_le_div_right (Nat.sub_le a b)
  exact lt_of_le_of_lt (Nat.size_le_size h) (half_size_lt a ha)

theorem even_double_half (a : Nat) (ha : a%2=0) : 2*(a/2)=a := by omega

theorem odd_gcd_two (a : Nat) (ha : a%2=1) : Nat.gcd 2 a=1 := by
  rw [Nat.gcd_rec,ha]
  rfl

theorem gcd_even_odd (a b : Nat) (ha : a%2=0) (hb : b%2=1) :
    Nat.gcd (a/2) b=Nat.gcd a b := by
  have h := Nat.gcd_mul_right_left_of_gcd_eq_one (n:=2) (m:=b) (k:=a/2) (odd_gcd_two b hb)
  rw [even_double_half a ha] at h
  exact h.symm

theorem gcd_odd_even (a b : Nat) (ha : a%2=1) (hb : b%2=0) :
    Nat.gcd a (b/2)=Nat.gcd a b := by
  simpa only [Nat.gcd_comm] using gcd_even_odd b a hb ha

theorem gcd_both_even (a b : Nat) (ha : a%2=0) (hb : b%2=0) :
    2*Nat.gcd (a/2) (b/2)=Nat.gcd a b := by
  have h := Nat.gcd_mul_left 2 (a/2) (b/2)
  rw [even_double_half a ha,even_double_half b hb] at h
  exact h.symm

theorem gcd_odd_sub_half (a b : Nat) (ha : a%2=1) (hb : b%2=1) (hle : b≤a) :
    Nat.gcd ((a-b)/2) b=Nat.gcd a b := by
  have he : (a-b)%2=0 := by omega
  rw [gcd_even_odd (a-b) b he hb,Nat.gcd_sub_self_left hle]

theorem gcd_odd_self_sub_half (a b : Nat) (ha : a%2=1) (hb : b%2=1) (hle : a≤b) :
    Nat.gcd a ((b-a)/2)=Nat.gcd a b := by
  simpa only [Nat.gcd_comm] using gcd_odd_sub_half b a hb ha hle

/-- Every nonterminal real Stein branch lowers this rank by at least one;
this bound is proof-only and is never runtime fuel or machine input. -/
theorem branch_rank (a b : Nat) (ha : a≠0) (hb : b≠0) :
    rank (a/2) b<rank a b ∧ rank a (b/2)<rank a b ∧
    rank (a/2) (b/2)<rank a b ∧ rank ((a-b)/2) b<rank a b ∧
    rank a ((b-a)/2)<rank a b := by
  have h1:=half_size_lt a ha
  have h2:=half_size_lt b hb
  have h3:=subtraction_half_size_lt a b ha
  have h4:=subtraction_half_size_lt b a hb
  unfold rank
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDSteinMath009
