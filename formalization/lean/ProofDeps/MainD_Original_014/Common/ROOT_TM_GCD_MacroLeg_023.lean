module
public import Common.ROOT_TM_GCD_SwapLeg_022

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDMacroLeg023
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006 ROOTTMGCDDispatch018 ROOTTMGCDLift020 ROOTTMGCDLeg021
open ROOTTMGCDPairStep019
local notation "cols" => PSTRTMBinaryAdd024.operandColumns
local notation "leftCols" => PSTRTMCompareCode054.leftColumns

def atEnd (phase : Fin 23) (n : Nat) (pairs : List Pair) (suffix : List Bool) : MachineState 3219 :=
  blockCfg (s:=139) phase ⟨0,Turing.Tape.mk₂ (leftCols pairs.reverse++false::ROOTTMGCDCounter011.ones n) (false::false::suffix)⟩
def subTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  (PA17TMDivisionSub001.residentSubTrace (ROOTTMGCDCounter011.ones n) pairs suffix).map (lift (by decide : 33 ≤ 139) 15)
theorem sub_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt 15 n pairs suffix) (subTrace n pairs suffix) (cfgAt 16 n (PA17TMDivisionSub001.subPairs false pairs) suffix) := by
  let archive:=ROOTTMGCDCounter011.ones n
  have run:=PA17TMDivisionSub001.residentSub_runsFrom archive pairs suffix
  have hf : family 15=padMachine (by decide : 33 ≤ 139) PA17TMDivisionSub001.residentSubMachine := rfl
  have hs:=phase_segment (by decide : 33 ≤ 139) 15 PA17TMDivisionSub001.residentSubMachine hf _ _ _ run
  have hp : ports 15 (padLabel (by decide : 33 ≤ 139) (PA17TMDivisionSub001.residentSubFinal archive pairs suffix).q)=some (16,0) := rfl
  have ht:=phase_transfer (by decide : 33 ≤ 139) 15 16 PA17TMDivisionSub001.residentSubMachine hf _ run.2.2.2 0 hp
  exact ⟨lift (by decide : 33 ≤ 139) 15 (PA17TMDivisionSub001.residentSubFinal archive pairs suffix),hs,ht⟩

def rewindTrace (phase : Fin 23) (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  (PSTRTMColumnRewind067.fullTrace (ROOTTMGCDCounter011.ones n) pairs.reverse (false::false::suffix)).map
    (lift (by decide : 5 ≤ 139) phase)
theorem rewind_leg (phase next : Fin 23)
    (hf : family phase=padMachine (by decide : 5 ≤ 139) PSTRTMColumnRewind067.rewindMachine)
    (hp : ports phase 5=some (next,0)) (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (atEnd phase n pairs suffix) (rewindTrace phase n pairs suffix) (cfgAt next n pairs suffix) := by
  let archive:=ROOTTMGCDCounter011.ones n
  have run:=PSTRTMColumnRewind067.rewind_runsFrom archive pairs (false::false::suffix)
  have hs:=phase_segment (by decide : 5 ≤ 139) phase PSTRTMColumnRewind067.rewindMachine hf _ _ _ run
  have ht:=phase_transfer (by decide : 5 ≤ 139) phase next PSTRTMColumnRewind067.rewindMachine hf _ run.2.2.2 0 hp
  exact ⟨lift (by decide : 5 ≤ 139) phase (PSTRTMColumnRewind067.state 5 (false::archive) (cols pairs++false::false::suffix)),hs,ht⟩

def counterTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  (ROOTTMGCDCounter011.fullTrace n (cols pairs++false::false::suffix)).map (lift (by decide : 5 ≤ 139) 10)
theorem counter_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt 10 n pairs suffix) (counterTrace n pairs suffix) (cfgAt 0 (n+1) pairs suffix) := by
  let tail:=cols pairs++false::false::suffix
  have run:=ROOTTMGCDCounter011.counter_runsFrom n tail
  have hf : family 10=padMachine (by decide : 5 ≤ 139) ROOTTMGCDCounter011.counterMachine := rfl
  have hs:=phase_segment (by decide : 5 ≤ 139) 10 ROOTTMGCDCounter011.counterMachine hf _ _ _ run
  have hp : ports 10 5=some (0,0) := rfl
  have ht:=phase_transfer (by decide : 5 ≤ 139) 10 0 ROOTTMGCDCounter011.counterMachine hf _ run.2.2.2 0 hp
  exact ⟨lift (by decide : 5 ≤ 139) 10 (ROOTTMGCDCounter011.state 5 (false::ROOTTMGCDCounter011.ones (n+1)) tail),hs,ht⟩

theorem subTrace_length (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (subTrace n pairs suffix).length=13*pairs.length+6 := by
  simp only [subTrace,List.length_map,PA17TMDivisionSub001.residentSub_length]
theorem rewindTrace_length (phase : Fin 23) (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (rewindTrace phase n pairs suffix).length=4*pairs.length+3 := by
  simp only [rewindTrace,List.length_map,PSTRTMColumnRewind067.full_length,List.length_reverse]
theorem counterTrace_length (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (counterTrace n pairs suffix).length=2*n+6 := by
  simp only [counterTrace,List.length_map,ROOTTMGCDCounter011.full_length]

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDMacroLeg023
