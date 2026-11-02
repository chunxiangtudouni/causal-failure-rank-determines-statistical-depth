module
public import Common.ROOT_TM_GCD_SteinMath_009

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDSteinStep015
open ROOTTMGCDSteinMath009

/-- Mathematical descriptor of the actual finite-control branch targets.
It supplies no machine opcode and is not accepted as an execution proof. -/
def nextPair (a b : Nat) : Nat × Nat :=
  if a%2=0 then if b%2=0 then (a/2,b/2) else (a/2,b)
  else if b%2=0 then (a,b/2)
  else if a<b then (a,(b-a)/2) else (b,(a-b)/2)
def nextTwos (a b k : Nat) : Nat := if a%2=0 ∧ b%2=0 then k+1 else k

theorem rank_decreases (a b : Nat) (ha : a≠0) (hb : b≠0) :
    rank (nextPair a b).1 (nextPair a b).2<rank a b := by
  have hs:=branch_rank a b ha hb
  unfold nextPair
  split_ifs with h1 h2 h3 h4
  · exact hs.2.2.1
  · exact hs.1
  · exact hs.2.1
  · exact hs.2.2.2.2
  · have h:=hs.2.2.2.1
    simpa only [rank,Nat.add_comm] using h

theorem scaled_gcd (a b k : Nat) :
    2^(nextTwos a b k)*Nat.gcd (nextPair a b).1 (nextPair a b).2=2^k*Nat.gcd a b := by
  by_cases he : a%2=0
  · by_cases hf : b%2=0
    · simp only [nextPair,nextTwos,he,hf,ite_true,and_self]
      rw [Nat.pow_succ]
      calc
        2^k*2*Nat.gcd (a/2) (b/2)=2^k*(2*Nat.gcd (a/2) (b/2)) := Nat.mul_assoc _ _ _
        _=2^k*Nat.gcd a b := by rw [gcd_both_even a b he hf]
    · have ho : b%2=1 := by omega
      simp only [nextPair,nextTwos,he,hf,ite_true,ite_false,and_false]
      rw [gcd_even_odd a b he ho]
  · have ho : a%2=1 := by omega
    by_cases hf : b%2=0
    · simp only [nextPair,nextTwos,he,hf,ite_true,ite_false,false_and]
      rw [gcd_odd_even a b ho hf]
    · have hp : b%2=1 := by omega
      by_cases hlt : a<b
      · simp only [nextPair,nextTwos,he,hf,hlt,ite_true,ite_false,false_and]
        rw [gcd_odd_self_sub_half a b ho hp (by omega)]
      · simp only [nextPair,nextTwos,he,hf,hlt,ite_false,false_and]
        rw [Nat.gcd_comm b,gcd_odd_sub_half a b ho hp (by omega)]

theorem next_values_le (a b : Nat) :
    (nextPair a b).1 ≤ max a b ∧ (nextPair a b).2 ≤ max a b := by
  have ha:=le_max_left a b
  have hb:=le_max_right a b
  unfold nextPair
  split_ifs <;> constructor <;> dsimp <;> omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDSteinStep015
