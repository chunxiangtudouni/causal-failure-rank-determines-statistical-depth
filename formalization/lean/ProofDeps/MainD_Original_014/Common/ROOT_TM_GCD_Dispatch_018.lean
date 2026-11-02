module
public import Common.ROOT_TM_GCD_ZeroResident_010
public import Common.ROOT_TM_GCD_PopTrace_017
public import Common.ROOT_TM_GCD_HalfResident_014
public import Common.ROOT_TM_GCD_SteinStep_015
public import Structure.PA17_TM_Division_Codec_003g

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDDispatch018
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006

/-- Twenty-three fixed phases, padded uniformly only at the code level.
No operand, width, fuel, gcd answer, branch decision or runtime bound occurs
in this finite machine definition. Operational composition remains to prove. -/
def family (phase : Fin 23) : Machine 139 :=
  match phase.val with
  | 0 => ROOTTMGCDZeroResident010.residentZeroMachine
  | 1 => padMachine (by decide : 12 ≤ 139) ROOTTMGCDParity013.parityMachine
  | 2 | 4 | 6 | 8 | 17 => padMachine (by decide : 52 ≤ 139) ROOTTMGCDHalfResident014.residentHalfMachine
  | 3 | 5 | 7 | 9 | 14 | 16 => padMachine (by decide : 36 ≤ 139)
      (ROOTTMGCDMap004.residentMapMachine ROOTTMGCDMap004.swapPair)
  | 10 => padMachine (by decide : 5 ≤ 139) ROOTTMGCDCounter011.counterMachine
  | 11 => padMachine (by decide : 20 ≤ 139) PSTRTMCompareCode054.compareMachine
  | 12 | 13 | 21 => padMachine (by decide : 5 ≤ 139) PSTRTMColumnRewind067.rewindMachine
  | 15 => padMachine (by decide : 33 ≤ 139) PA17TMDivisionSub001.residentSubMachine
  | 18 => padMachine (by decide : 36 ≤ 139)
      (ROOTTMGCDMap004.residentMapMachine ROOTTMGCDMap004.outputPair)
  | 19 => padMachine (by decide : 7 ≤ 139) ROOTTMGCDPop016.popMachine
  | 20 => padMachine (by decide : 19 ≤ 139) PSTRTMShiftColumnCode065.shiftMachine
  | _ => padMachine (by decide : 103 ≤ 139) PA17TMDivisionCodec003.isolatedOutputMachine

def ports (phase : Fin 23) (q : Fin 140) : Option (Fin 23 × Fin 140) :=
  match phase.val with
  | 0 => if q.val=117 then some (1,0) else
      if q.val=33 ∨ q.val=61 ∨ q.val=89 then some (18,0) else none
  | 1 => if q.val=9 then some (6,0) else if q.val=10 then some (3,0)
      else if q.val=11 then some (2,0) else if q.val=12 then some (11,0) else none
  | 2 => if 49 ≤ q.val ∧ q.val ≤ 52 then some (0,0) else none
  | 3 => if q.val=36 then some (4,0) else none
  | 4 => if 49 ≤ q.val ∧ q.val ≤ 52 then some (5,0) else none
  | 5 => if q.val=36 then some (0,0) else none
  | 6 => if 49 ≤ q.val ∧ q.val ≤ 52 then some (7,0) else none
  | 7 => if q.val=36 then some (8,0) else none
  | 8 => if 49 ≤ q.val ∧ q.val ≤ 52 then some (9,0) else none
  | 9 => if q.val=36 then some (10,0) else none
  | 10 => if q.val=5 then some (0,0) else none
  | 11 => if q.val=19 then some (12,0) else if q.val=18 ∨ q.val=20 then some (13,0) else none
  | 12 => if q.val=5 then some (14,0) else none
  | 13 => if q.val=5 then some (15,0) else none
  | 14 => if q.val=36 then some (15,0) else none
  | 15 => if q.val=33 then some (16,0) else none
  | 16 => if q.val=36 then some (17,0) else none
  | 17 => if 49 ≤ q.val ∧ q.val ≤ 52 then some (0,0) else none
  | 18 => if q.val=36 then some (19,0) else none
  | 19 => if q.val=6 then some (20,0) else if q.val=7 then some (22,0) else none
  | 20 => if q.val=18 then some (21,0) else none
  | 21 => if q.val=5 then some (19,0) else none
  | _ => none

/-- One fixed3220-label resident Stein dispatcher. No claim of execution,
correctness, termination or cost is inferred from this code declaration. -/
def residentGcdMachine : Machine 3219 := blockMachine family ports

/-- One fixed3565-label original-input machine. The raw two-Nat codec is
actually part of the program, before the resident dispatcher. -/
def nativeGcdMachine : Machine 3564 :=
  PSTRTMSeq005.seqMachine PSTRTMRawPack045.rawPackMachine residentGcdMachine

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDDispatch018
