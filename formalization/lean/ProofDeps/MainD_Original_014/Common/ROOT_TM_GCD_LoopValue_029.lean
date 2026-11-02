module
public import Common.ROOT_TM_GCD_Loop_028

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDLoopValue029
open PaperProofs.Common.Native.RationalControllerComputation
open ROOTTMGCDPairStep019 ROOTTMGCDSteinMath009 ROOTTMGCDLoop028
local notation "AVal" => PSTRTMBinaryAdd024.firstValue
local notation "BVal" => PSTRTMBinaryAdd024.secondValue

theorem loop_specs (fuel n : Nat) (pairs : List Pair) (suffix : List Bool)
    (hrank : rank (AVal pairs) (BVal pairs) ≤ fuel) :
    let out:=loopData fuel n pairs suffix
    (AVal out.pairs=0 ∨ BVal out.pairs=0) ∧ out.pairs.length=pairs.length ∧ out.twos ≤ n+fuel ∧
      2^out.twos*Nat.gcd (AVal out.pairs) (BVal out.pairs)=2^n*Nat.gcd (AVal pairs) (BVal pairs) := by
  induction fuel generalizing n pairs with
  | zero =>
    have hs : (AVal pairs).size=0 := by unfold rank at hrank;omega
    have ha : AVal pairs=0 := Nat.size_eq_zero.mp hs
    dsimp only [loopData]
    exact ⟨Or.inl ha,rfl,by omega,rfl⟩
  | succ fuel ih =>
    by_cases hz : AVal pairs=0 ∨ BVal pairs=0
    · simpa only [loopData,ite_eq_left hz] using
        (show (AVal pairs=0 ∨ BVal pairs=0) ∧ pairs.length=pairs.length ∧ n ≤ n+(fuel+1) ∧
          2^n*Nat.gcd (AVal pairs) (BVal pairs)=2^n*Nat.gcd (AVal pairs) (BVal pairs) from ⟨hz,rfl,by omega,rfl⟩)
    · have ha : AVal pairs≠0 := fun h=>hz (Or.inl h)
      have hb : BVal pairs≠0 := fun h=>hz (Or.inr h)
      have hv:=next_values pairs
      have hv1 : AVal (nextPairs pairs)=(ROOTTMGCDSteinStep015.nextPair (AVal pairs) (BVal pairs)).1 := congrArg Prod.fst hv
      have hv2 : BVal (nextPairs pairs)=(ROOTTMGCDSteinStep015.nextPair (AVal pairs) (BVal pairs)).2 := congrArg Prod.snd hv
      have hnext:=ROOTTMGCDSteinStep015.rank_decreases (AVal pairs) (BVal pairs) ha hb
      have hbound : rank (AVal (nextPairs pairs)) (BVal (nextPairs pairs)) ≤ fuel := by
        rw [hv1,hv2]
        omega
      let n':=ROOTTMGCDSteinStep015.nextTwos (AVal pairs) (BVal pairs) n
      have hn : n' ≤ n+1 := by unfold n' ROOTTMGCDSteinStep015.nextTwos;split_ifs <;> omega
      have hrec:=ih n' (nextPairs pairs) hbound
      have hg:=ROOTTMGCDSteinStep015.scaled_gcd (AVal pairs) (BVal pairs) n
      rw [←hv1,←hv2] at hg
      have hlen:=next_length pairs
      simp only [loopData,ite_eq_right hz]
      refine ⟨hrec.1,hrec.2.1.trans hlen,?_,hrec.2.2.2.trans hg⟩
      exact hrec.2.2.1.trans (by omega)

theorem terminal_gcd_sum (pairs : List Pair) (hz : AVal pairs=0 ∨ BVal pairs=0) :
    Nat.gcd (AVal pairs) (BVal pairs)=AVal pairs+BVal pairs := by
  cases hz with
  | inl ha => simp only [ha,Nat.gcd_zero_left,Nat.zero_add]
  | inr hb => simp only [hb,Nat.gcd_zero_right,Nat.add_zero]

theorem gcd_le_max (a b : Nat) : Nat.gcd a b ≤ max a b := by
  by_cases ha : a=0
  · simp only [ha,Nat.gcd_zero_left,Nat.zero_max,le_refl]
  · exact (Nat.gcd_le_left b (by omega)).trans (le_max_left a b)

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDLoopValue029
