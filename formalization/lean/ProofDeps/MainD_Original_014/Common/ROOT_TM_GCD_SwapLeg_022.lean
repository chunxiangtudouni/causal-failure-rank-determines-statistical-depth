module
public import Common.ROOT_TM_GCD_Leg_021

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDSwapLeg022
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006 ROOTTMGCDDispatch018 ROOTTMGCDLift020 ROOTTMGCDLeg021
open ROOTTMGCDPairStep019

def swapTrace (phase : Fin 23) (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  (ROOTTMGCDMap004.residentMapTrace ROOTTMGCDMap004.swapPair (ROOTTMGCDCounter011.ones n) pairs suffix).map
    (lift (by decide : 36 ≤ 139) phase)
theorem swap_leg (phase next : Fin 23)
    (hf : family phase=padMachine (by decide : 36 ≤ 139) (ROOTTMGCDMap004.residentMapMachine ROOTTMGCDMap004.swapPair))
    (hp : ports phase 36=some (next,0)) (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt phase n pairs suffix) (swapTrace phase n pairs suffix) (cfgAt next n (swap pairs) suffix) := by
  let archive:=ROOTTMGCDCounter011.ones n
  have run:=ROOTTMGCDMap004.residentMap_runsFrom ROOTTMGCDMap004.swapPair archive pairs suffix
  have hs:=phase_segment (by decide : 36 ≤ 139) phase (ROOTTMGCDMap004.residentMapMachine ROOTTMGCDMap004.swapPair)
    hf _ _ _ run
  have ht:=phase_transfer (by decide : 36 ≤ 139) phase next (ROOTTMGCDMap004.residentMapMachine ROOTTMGCDMap004.swapPair)
    hf _ run.2.2.2 0 hp
  exact ⟨lift (by decide : 36 ≤ 139) phase (ROOTTMGCDMap004.residentMapFinal ROOTTMGCDMap004.swapPair archive pairs suffix),hs,ht⟩
theorem swapTrace_length (phase : Fin 23) (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (swapTrace phase n pairs suffix).length=14*pairs.length+6 := by
  simp only [swapTrace,List.length_map,ROOTTMGCDMap004.residentMap_length]

def evenATrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  swapTrace 3 n pairs suffix++halfTrace 4 n (swap pairs) suffix++swapTrace 5 n (half (swap pairs)) suffix

/-- All three literal phases really execute on the same tape; the final
port returns to the actual classifier entry. No branch/cost oracle is used. -/
theorem evenA_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt 3 n pairs suffix) (evenATrace n pairs suffix) (cfgAt 0 n (halfA pairs) suffix) := by
  have h1:=swap_leg 3 4 rfl rfl n pairs suffix
  have h2 : Leg (cfgAt 4 n (swap pairs) suffix) (halfTrace 4 n (swap pairs) suffix)
      (cfgAt 5 n (half (swap pairs)) suffix) := by
    apply half_leg 4 5 rfl
    intro r
    have hr:=r.isLt
    simp [ports,show 49 ≤ 49+r.val by omega,show 49+r.val ≤ 52 by omega]
  have h3:=swap_leg 5 0 rfl rfl n (half (swap pairs)) suffix
  exact Leg.append _ _ _ _ _ (Leg.append _ _ _ _ _ h1 h2) h3

theorem evenATrace_length (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (evenATrace n pairs suffix).length=37*pairs.length+18 := by
  simp only [evenATrace,List.length_append,swapTrace_length,halfTrace_length,swap_length,half_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDSwapLeg022
