module
public import Common.ROOT_TM_GCD_RoundLeg_027

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDLoop028
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006 ROOTTMGCDDispatch018 ROOTTMGCDLeg021 ROOTTMGCDDispatchLeg025
open ROOTTMGCDControlValue026 ROOTTMGCDPairStep019 ROOTTMGCDRoundLeg027 ROOTTMGCDSteinMath009
local notation "AVal" => PSTRTMBinaryAdd024.firstValue
local notation "BVal" => PSTRTMBinaryAdd024.secondValue

structure Result where
  trace : List (MachineState 3219)
  twos : Nat
  pairs : List Pair

/-- This decreasing fuel is ONLY a proof witness for the existential
trace. It is absent from the actual fixed machine and its original input. -/
def loopData : Nat → Nat → List Pair → List Bool → Result
  | 0,n,pairs,suffix => ⟨zeroTrace n pairs suffix,n,pairs⟩
  | fuel+1,n,pairs,suffix =>
    if AVal pairs=0 ∨ BVal pairs=0 then ⟨zeroTrace n pairs suffix,n,pairs⟩ else
      let later:=loopData fuel (ROOTTMGCDSteinStep015.nextTwos (AVal pairs) (BVal pairs) n) (nextPairs pairs) suffix
      ⟨roundTrace n pairs suffix++later.trace,later.twos,later.pairs⟩

theorem zero_leg_exit (n : Nat) (pairs : List Pair) (suffix : List Bool)
    (hz : AVal pairs=0 ∨ BVal pairs=0) :
    Leg (cfgAt 0 n pairs suffix) (zeroTrace n pairs suffix) (cfgAt 18 n pairs suffix) := by
  have h:=zero_leg n pairs suffix
  have hc:=zero_control_not_three pairs hz
  simpa only [zeroNext,ite_eq_right hc] using h

/-- Full actual finite-control execution through all Stein rounds to the
real output phase. No user input or callee supplies a loop clock/rank. -/
theorem loop_leg (fuel n : Nat) (pairs : List Pair) (suffix : List Bool)
    (hrank : rank (AVal pairs) (BVal pairs) ≤ fuel) :
    Leg (cfgAt 0 n pairs suffix) (loopData fuel n pairs suffix).trace
      (cfgAt 18 (loopData fuel n pairs suffix).twos (loopData fuel n pairs suffix).pairs suffix) := by
  induction fuel generalizing n pairs with
  | zero =>
    have hs : (AVal pairs).size=0 := by unfold rank at hrank;omega
    have ha : AVal pairs=0 := Nat.size_eq_zero.mp hs
    exact zero_leg_exit n pairs suffix (Or.inl ha)
  | succ fuel ih =>
    by_cases hz : AVal pairs=0 ∨ BVal pairs=0
    · simpa only [loopData,ite_eq_left hz] using zero_leg_exit n pairs suffix hz
    · have ha : AVal pairs≠0 := fun h=>hz (Or.inl h)
      have hb : BVal pairs≠0 := fun h=>hz (Or.inr h)
      have hnext:=ROOTTMGCDSteinStep015.rank_decreases (AVal pairs) (BVal pairs) ha hb
      have hv:=next_values pairs
      have hv1 : AVal (nextPairs pairs)=(ROOTTMGCDSteinStep015.nextPair (AVal pairs) (BVal pairs)).1 := congrArg Prod.fst hv
      have hv2 : BVal (nextPairs pairs)=(ROOTTMGCDSteinStep015.nextPair (AVal pairs) (BVal pairs)).2 := congrArg Prod.snd hv
      have hbound : rank (AVal (nextPairs pairs)) (BVal (nextPairs pairs)) ≤ fuel := by
        rw [hv1,hv2]
        omega
      have h1:=round_leg n pairs suffix ha hb
      have h2:=ih (ROOTTMGCDSteinStep015.nextTwos (AVal pairs) (BVal pairs) n) (nextPairs pairs) hbound
      simpa only [loopData,ite_eq_right hz] using Leg.append _ _ _ _ _ h1 h2

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDLoop028
