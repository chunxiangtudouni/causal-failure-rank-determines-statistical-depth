module
public import Common.ROOT_TM_GCD_MacroLeg_023

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDBranchLeg024
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006 ROOTTMGCDDispatch018 ROOTTMGCDLeg021 ROOTTMGCDSwapLeg022 ROOTTMGCDMacroLeg023
open ROOTTMGCDPairStep019

def bothTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  halfTrace 6 n pairs suffix++swapTrace 7 n (half pairs) suffix++
    halfTrace 8 n (swap (half pairs)) suffix++swapTrace 9 n (half (swap (half pairs))) suffix++
    counterTrace n (halfBoth pairs) suffix
theorem both_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt 6 n pairs suffix) (bothTrace n pairs suffix) (cfgAt 0 (n+1) (halfBoth pairs) suffix) := by
  have h1 : Leg (cfgAt 6 n pairs suffix) (halfTrace 6 n pairs suffix) (cfgAt 7 n (half pairs) suffix) := by
    apply half_leg 6 7 rfl
    intro r
    have hr:=r.isLt
    simp [ports,show 49 ≤ 49+r.val by omega,show 49+r.val ≤ 52 by omega]
  have h2:=swap_leg 7 8 rfl rfl n (half pairs) suffix
  have h3 : Leg (cfgAt 8 n (swap (half pairs)) suffix) (halfTrace 8 n (swap (half pairs)) suffix)
      (cfgAt 9 n (half (swap (half pairs))) suffix) := by
    apply half_leg 8 9 rfl
    intro r
    have hr:=r.isLt
    simp [ports,show 49 ≤ 49+r.val by omega,show 49+r.val ≤ 52 by omega]
  have h4:=swap_leg 9 10 rfl rfl n (half (swap (half pairs))) suffix
  have h5:=counter_leg n (halfBoth pairs) suffix
  exact Leg.append _ _ _ _ _ (Leg.append _ _ _ _ _ (Leg.append _ _ _ _ _ (Leg.append _ _ _ _ _ h1 h2) h3) h4) h5

def oddTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  subTrace n pairs suffix++swapTrace 16 n (PA17TMDivisionSub001.subPairs false pairs) suffix++
    halfTrace 17 n (swap (PA17TMDivisionSub001.subPairs false pairs)) suffix
theorem odd_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt 15 n pairs suffix) (oddTrace n pairs suffix) (cfgAt 0 n (oddGreater pairs) suffix) := by
  have h1:=sub_leg n pairs suffix
  have h2:=swap_leg 16 17 rfl rfl n (PA17TMDivisionSub001.subPairs false pairs) suffix
  have h3 : Leg (cfgAt 17 n (swap (PA17TMDivisionSub001.subPairs false pairs)) suffix)
      (halfTrace 17 n (swap (PA17TMDivisionSub001.subPairs false pairs)) suffix)
      (cfgAt 0 n (oddGreater pairs) suffix) := by
    apply half_leg 17 0 rfl
    intro r
    have hr:=r.isLt
    simp [ports,show 49 ≤ 49+r.val by omega,show 49+r.val ≤ 52 by omega]
  exact Leg.append _ _ _ _ _ (Leg.append _ _ _ _ _ h1 h2) h3

def lessTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  rewindTrace 12 n pairs suffix++swapTrace 14 n pairs suffix++oddTrace n (swap pairs) suffix
theorem less_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (atEnd 12 n pairs suffix) (lessTrace n pairs suffix) (cfgAt 0 n (oddLess pairs) suffix) := by
  have h1:=rewind_leg 12 14 rfl rfl n pairs suffix
  have h2:=swap_leg 14 15 rfl rfl n pairs suffix
  have h3:=odd_leg n (swap pairs) suffix
  exact Leg.append _ _ _ _ _ (Leg.append _ _ _ _ _ h1 h2) h3

def greaterTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  rewindTrace 13 n pairs suffix++oddTrace n pairs suffix
theorem greater_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (atEnd 13 n pairs suffix) (greaterTrace n pairs suffix) (cfgAt 0 n (oddGreater pairs) suffix) :=
  Leg.append _ _ _ _ _ (rewind_leg 13 15 rfl rfl n pairs suffix) (odd_leg n pairs suffix)

theorem bothTrace_length (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (bothTrace n pairs suffix).length=46*pairs.length+2*n+30 := by
  simp only [bothTrace,List.length_append,halfTrace_length,swapTrace_length,counterTrace_length,
    half_length,swap_length]
  omega
theorem oddTrace_length (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (oddTrace n pairs suffix).length=36*pairs.length+18 := by
  simp only [oddTrace,List.length_append,subTrace_length,swapTrace_length,halfTrace_length,
    swap_length,PA17TMDivisionSub001.subPairs_length]
  omega
theorem lessTrace_length (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (lessTrace n pairs suffix).length=54*pairs.length+27 := by
  simp only [lessTrace,List.length_append,rewindTrace_length,swapTrace_length,oddTrace_length,swap_length]
  omega
theorem greaterTrace_length (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (greaterTrace n pairs suffix).length=40*pairs.length+21 := by
  simp only [greaterTrace,List.length_append,rewindTrace_length,oddTrace_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDBranchLeg024
