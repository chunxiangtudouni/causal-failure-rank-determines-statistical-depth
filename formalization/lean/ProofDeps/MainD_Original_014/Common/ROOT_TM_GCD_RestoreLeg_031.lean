module
public import Common.ROOT_TM_GCD_Output_030

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDRestoreLeg031
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006 ROOTTMGCDDispatch018 ROOTTMGCDLift020 ROOTTMGCDLeg021 ROOTTMGCDMacroLeg023 ROOTTMGCDPairStep019
local notation "cols" => PSTRTMBinaryAdd024.operandColumns
local notation "leftCols" => PSTRTMCompareCode054.leftColumns

def popSuccTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  (ROOTTMGCDPop016.succTrace n (cols pairs++false::false::suffix)).map (lift (by decide : 7 ≤ 139) 19)
def popZeroTrace (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  (ROOTTMGCDPop016.zeroTrace (cols pairs++false::false::suffix)).map (lift (by decide : 7 ≤ 139) 19)
theorem pop_succ_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt 19 (n+1) pairs suffix) (popSuccTrace n pairs suffix) (cfgAt 20 n pairs suffix) := by
  let tail:=cols pairs++false::false::suffix
  have run:=ROOTTMGCDPop016.pop_succ_runsFrom n tail
  have hf : family 19=padMachine (by decide : 7 ≤ 139) ROOTTMGCDPop016.popMachine := rfl
  have hs:=phase_segment (by decide : 7 ≤ 139) 19 ROOTTMGCDPop016.popMachine hf _ _ _ run
  have ht:=phase_transfer (by decide : 7 ≤ 139) 19 20 ROOTTMGCDPop016.popMachine hf _ run.2.2.2 0 rfl
  exact ⟨lift (by decide : 7 ≤ 139) 19 (ROOTTMGCDPop016.state 6 (false::ROOTTMGCDPop016.ones n) tail),hs,ht⟩
theorem pop_zero_leg (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt 19 0 pairs suffix) (popZeroTrace pairs suffix) (cfgAt 22 0 pairs suffix) := by
  let tail:=cols pairs++false::false::suffix
  have run:=ROOTTMGCDPop016.pop_zero_runsFrom tail
  have hf : family 19=padMachine (by decide : 7 ≤ 139) ROOTTMGCDPop016.popMachine := rfl
  have hs:=phase_segment (by decide : 7 ≤ 139) 19 ROOTTMGCDPop016.popMachine hf _ _ _ run
  have ht:=phase_transfer (by decide : 7 ≤ 139) 19 22 ROOTTMGCDPop016.popMachine hf _ run.2.2.2 0 rfl
  exact ⟨lift (by decide : 7 ≤ 139) 19 (ROOTTMGCDPop016.state 7 [false] tail),hs,ht⟩

def shiftTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  (PSTRTMShiftColumnTrace066.shiftTrace false (false::ROOTTMGCDCounter011.ones n) [] pairs suffix).map
    (lift (by decide : 19 ≤ 139) 20)
theorem shift_leg (n : Nat) (pairs : List Pair) (suffix : List Bool)
    (hc : PSTRTMShiftColumnCode065.finalCarry false pairs=false) :
    Leg (cfgAt 20 n pairs suffix) (shiftTrace n pairs suffix)
      (atEnd 21 n (PSTRTMShiftColumnCode065.shiftPairs false pairs) suffix) := by
  let archive:=ROOTTMGCDCounter011.ones n
  let last:=PSTRTMShiftColumnCode065.state (PSTRTMShiftColumnCode065.haltLabel (PSTRTMShiftColumnCode065.finalCarry false pairs))
    (leftCols (PSTRTMShiftColumnCode065.shiftPairs false pairs).reverse++false::archive) (false::false::suffix)
  have run:=PSTRTMShiftColumnTrace066.shift_runsFrom false (false::archive) pairs suffix
  have hf : family 20=padMachine (by decide : 19 ≤ 139) PSTRTMShiftColumnCode065.shiftMachine := rfl
  have hs:=phase_segment (by decide : 19 ≤ 139) 20 PSTRTMShiftColumnCode065.shiftMachine hf _ _ _ run
  have hp : ports 20 (padLabel (by decide : 19 ≤ 139) last.q)=some (21,0) := by
    change ports 20 (padLabel (by decide : 19 ≤ 139)
      (PSTRTMShiftColumnCode065.haltLabel (PSTRTMShiftColumnCode065.finalCarry false pairs)))=some (21,0)
    rw [hc]
    rfl
  have ht:=phase_transfer (by decide : 19 ≤ 139) 20 21 PSTRTMShiftColumnCode065.shiftMachine hf last run.2.2.2 0 hp
  exact ⟨lift (by decide : 19 ≤ 139) 20 last,hs,ht⟩

def restoreStepTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  popSuccTrace n pairs suffix++shiftTrace n pairs suffix++
    rewindTrace 21 n (PSTRTMShiftColumnCode065.shiftPairs false pairs) suffix
theorem restoreStep_leg (n : Nat) (pairs : List Pair) (suffix : List Bool)
    (hc : PSTRTMShiftColumnCode065.finalCarry false pairs=false) :
    Leg (cfgAt 19 (n+1) pairs suffix) (restoreStepTrace n pairs suffix)
      (cfgAt 19 n (PSTRTMShiftColumnCode065.shiftPairs false pairs) suffix) :=
  Leg.append _ _ _ _ _ (Leg.append _ _ _ _ _ (pop_succ_leg n pairs suffix) (shift_leg n pairs suffix hc))
    (rewind_leg 21 19 rfl rfl n (PSTRTMShiftColumnCode065.shiftPairs false pairs) suffix)

theorem restoreStepTrace_length (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (restoreStepTrace n pairs suffix).length=11*pairs.length+2*n+14 := by
  simp only [restoreStepTrace,popSuccTrace,shiftTrace,List.length_append,List.length_map,
    ROOTTMGCDPop016.succ_length,PSTRTMShiftColumnTrace066.shift_length,rewindTrace_length,
    PSTRTMShiftColumnCode065.shiftPairs_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDRestoreLeg031
