module
public import Structure.PA17_TM_Division_Sub_001b
public import Common.ROOT_TM_GCD_MapTrace_005
public import Structure.PA17_TM_Division_Codec_003g
public import Structure.PA17_TM_Division_Compose_006a
public import Common.PSTR_TM_NativeAdd_053

/-! Original raw two-Nat saturating subtraction. Borrow is read from the
actual old subtraction HALT26/27, not supplied by the input. Four fixed phases
retain this branch until a real zero-map has run when underflow occurred. -/

@[expose] public section
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016
open PA17TMDivisionCompose006

abbrev Pair := Bool × Bool
def zeroPair (_ : Pair) : Pair := (false,false)

def family (phase : Fin 4) : Machine 36 :=
  match phase.val with
  | 0 => padMachine (by decide : 27 ≤ 36) PA17TMDivisionSub001.subMachine
  | 1 | 2 => padMachine (by decide : 5 ≤ 36) PSTRTMColumnRewind067.rewindMachine
  | _ => padMachine (by decide : 36 ≤ 36) (ROOTTMGCDMap004.residentMapMachine zeroPair)

def ports (phase : Fin 4) (q : Fin 37) : Option (Fin 4 × Fin 37) :=
  match phase.val with
  | 0 => if q.val = 26 then some (1,0) else if q.val = 27 then some (2,0) else none
  | 2 => if q.val = 5 then some (3,0) else none
  | _ => none

/-- Fixed148-label actual borrow dispatcher. No operand, answer, width,
borrow decision, padding size, fuel or cost occurs in this code. -/
def branchMachine : Machine 147 := blockMachine family ports

/-- Existing104-label projection/canonical codec reads the actual first
track and clears B, trims high zeros including zero, and emits encodeNat. -/
def decodedMachine : Machine 251 :=
  PSTRTMSeq005.seqMachine branchMachine PA17TMDivisionCodec003.isolatedOutputMachine

/-- One fixed597-label Bool TM0 precedes every original pair of Nat inputs.
The entire raw codec/zero extension is part of the actual program. -/
def nativeSubMachine : Machine 596 :=
  PSTRTMSeq005.seqMachine PSTRTMRawPack045.rawPackMachine decodedMachine

def lift {states : Nat} (h : states ≤ 36) (phase : Fin 4) (old : MachineState states) : MachineState 147 :=
  blockCfg phase (padCfg h old)

def rewindPhase (borrow : Bool) : Fin 4 := if borrow then 2 else 1
def afterSub (pairs : List Pair) : List Pair := PA17TMDivisionSub001.subPairs false pairs
def borrow (pairs : List Pair) : Bool := PA17TMDivisionSub001.finalBorrow false pairs
def saturatedPairs (pairs : List Pair) : List Pair :=
  if borrow pairs then (afterSub pairs).map zeroPair else afterSub pairs

theorem family_sub : family 0 = padMachine (by decide : 27 ≤ 36) PA17TMDivisionSub001.subMachine := rfl

theorem family_rewind (b : Bool) :
    family (rewindPhase b) = padMachine (by decide : 5 ≤ 36) PSTRTMColumnRewind067.rewindMachine := by
  cases b <;> rfl

theorem family_zero :
    family 3 = padMachine (by decide : 36 ≤ 36) (ROOTTMGCDMap004.residentMapMachine zeroPair) := rfl

theorem borrow_port (b : Bool) :
    ports 0 (padLabel (by decide : 27 ≤ 36) (PA17TMDivisionSub001.haltLabel b)) = some (rewindPhase b,0) := by
  cases b <;> rfl

theorem rewind_nonborrow_halt_port : ports 1 (padLabel (by decide : 5 ≤ 36) 5) = none := rfl
theorem rewind_borrow_port : ports 2 (padLabel (by decide : 5 ≤ 36) 5) = some (3,0) := rfl
theorem zero_halt_port : ports 3 (padLabel (by decide : 36 ≤ 36) 36) = none := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016
