module
public import Common.ROOT_TM_GCD_BranchLeg_024

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDDispatchLeg025
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006 ROOTTMGCDDispatch018 ROOTTMGCDLift020 ROOTTMGCDLeg021 ROOTTMGCDMacroLeg023
open ROOTTMGCDPairStep019
local notation "cols" => PSTRTMBinaryAdd024.operandColumns
local notation "leftCols" => PSTRTMCompareCode054.leftColumns

def parityNext (a b : Bool) : Fin 23:=if a then if b then 11 else 2 else if b then 3 else 6
def parityTrace (n : Nat) (a b : Bool) (later : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  (ROOTTMGCDParity013.pairTrace a b (false::ROOTTMGCDCounter011.ones n) (cols later++false::false::suffix)).map
    (lift (by decide : 12 ≤ 139) 1)
theorem parity_leg (n : Nat) (a b : Bool) (later : List Pair) (suffix : List Bool) :
    Leg (cfgAt 1 n ((a,b)::later) suffix) (parityTrace n a b later suffix)
      (cfgAt (parityNext a b) n ((a,b)::later) suffix) := by
  let left:=false::ROOTTMGCDCounter011.ones n
  let right:=cols later++false::false::suffix
  have run:=ROOTTMGCDParity013.pair_runsFrom a b left right
  have hf : family 1=padMachine (by decide : 12 ≤ 139) ROOTTMGCDParity013.parityMachine := rfl
  have hs:=phase_segment (by decide : 12 ≤ 139) 1 ROOTTMGCDParity013.parityMachine hf _ _ _ run
  have hp : ports 1 (padLabel (by decide : 12 ≤ 139) (ROOTTMGCDParity013.haltLabel (ROOTTMGCDParity013.control a b)))=
      some (parityNext a b,0) := by cases a <;> cases b <;> rfl
  have ht:=phase_transfer (by decide : 12 ≤ 139) 1 (parityNext a b) ROOTTMGCDParity013.parityMachine
    hf _ run.2.2.2 0 hp
  exact ⟨lift (by decide : 12 ≤ 139) 1 (ROOTTMGCDParity013.state
    (ROOTTMGCDParity013.haltLabel (ROOTTMGCDParity013.control a b)) left (a::true::b::true::right)),hs,ht⟩

def zeroNext (r : Fin 4) : Fin 23:=if r.val=3 then 1 else 18
theorem zero_port (r : Fin 4) :
    ports 0 (label (ROOTTMGCDZeroResident010.rewindPhase r) (padLabel (by decide : 5 ≤ 27) 5))=some (zeroNext r,0) := by
  fin_cases r <;> rfl
def zeroTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  (ROOTTMGCDZeroResident010.trace (ROOTTMGCDCounter011.ones n) pairs suffix).map (blockCfg (s:=139) (0 : Fin 23))
theorem zero_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt 0 n pairs suffix) (zeroTrace n pairs suffix)
      (cfgAt (zeroNext (ROOTTMGCDZero006.resultControl 0 pairs)) n pairs suffix) := by
  let archive:=ROOTTMGCDCounter011.ones n
  let r:=ROOTTMGCDZero006.resultControl 0 pairs
  have run:=ROOTTMGCDZeroResident010.residentZero_runsFrom archive pairs suffix
  have hf : family 0=ROOTTMGCDZeroResident010.residentZeroMachine := rfl
  have run' : PSTRTMSeq005.RunsFrom (family 0) (ROOTTMGCDZeroResident010.initial archive pairs suffix)
      (ROOTTMGCDZeroResident010.trace archive pairs suffix) (ROOTTMGCDZeroResident010.final archive pairs suffix) := by
    rw [hf]
    exact run
  have hs:=block_segment family ports 0 _ _ _ run'
  have hp : ports 0 (ROOTTMGCDZeroResident010.final archive pairs suffix).q=some (zeroNext r,0) := by
    change ports 0 (label (ROOTTMGCDZeroResident010.rewindPhase r) (padLabel (by decide : 5 ≤ 27) 5))=some (zeroNext r,0)
    exact zero_port r
  have ht:=block_transfer family ports 0 (ROOTTMGCDZeroResident010.final archive pairs suffix)
    (zeroNext r,0) run'.2.2.2 hp
  exact ⟨blockCfg (s:=139) (0 : Fin 23) (ROOTTMGCDZeroResident010.final archive pairs suffix),hs,ht⟩

def compareNext (r : Fin 3) : Fin 23:=if r.val=1 then 12 else 13
theorem compare_port (r : Fin 3) :
    ports 11 (padLabel (by decide : 20 ≤ 139) (PSTRTMCompareCode054.haltLabel r))=some (compareNext r,0) := by
  fin_cases r <;> rfl
def compareTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  (PSTRTMCompareTrace055.compareTrace 0 (false::ROOTTMGCDCounter011.ones n) [] pairs suffix).map
    (lift (by decide : 20 ≤ 139) 11)
theorem compare_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt 11 n pairs suffix) (compareTrace n pairs suffix)
      (atEnd (compareNext (PSTRTMCompareCode054.resultRelation 0 pairs)) n pairs suffix) := by
  let archive:=ROOTTMGCDCounter011.ones n
  let r:=PSTRTMCompareCode054.resultRelation 0 pairs
  let last:=PSTRTMCompareCode054.state (PSTRTMCompareCode054.haltLabel r)
    (leftCols pairs.reverse++false::archive) (false::false::suffix)
  have run:=PSTRTMCompareTrace055.compare_runsFrom 0 (false::archive) pairs suffix
  have hf : family 11=padMachine (by decide : 20 ≤ 139) PSTRTMCompareCode054.compareMachine := rfl
  have hs:=phase_segment (by decide : 20 ≤ 139) 11 PSTRTMCompareCode054.compareMachine hf _ _ _ run
  have hp : ports 11 (padLabel (by decide : 20 ≤ 139) last.q)=some (compareNext r,0) := by
    change ports 11 (padLabel (by decide : 20 ≤ 139) (PSTRTMCompareCode054.haltLabel r))=some (compareNext r,0)
    exact compare_port r
  have ht:=phase_transfer (by decide : 20 ≤ 139) 11 (compareNext r) PSTRTMCompareCode054.compareMachine
    hf last run.2.2.2 0 hp
  exact ⟨lift (by decide : 20 ≤ 139) 11 last,hs,ht⟩

theorem zeroTrace_length (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (zeroTrace n pairs suffix).length=8*pairs.length+6 := by
  simp only [zeroTrace,List.length_map,ROOTTMGCDZeroResident010.residentZero_length]
theorem parityTrace_length (n : Nat) (a b : Bool) (later : List Pair) (suffix : List Bool) :
    (parityTrace n a b later suffix).length=5 := rfl
theorem compareTrace_length (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (compareTrace n pairs suffix).length=4*pairs.length+3 := by
  simp only [compareTrace,List.length_map,PSTRTMCompareTrace055.compare_length]

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDDispatchLeg025
