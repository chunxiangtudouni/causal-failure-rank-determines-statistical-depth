module
public import Structure.PA17_TM_RatArithmetic_PairInput_050a
public import Structure.PA17_TM_RatArithmetic_WideCache_045b
public import Structure.PA17_TM_RatArithmetic_ReturnHome_037b

/-! The first actual native multiplication cycle. All operand values,
gaps and records describe physical tape states; code is chosen only by
fixed source fields and a finite bound on retained control memory. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstMul051

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticPairInput050
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticReturnHome037

def pairNativeRow (fieldA fieldB : SourceField) (memory : Nat) : Machine 2026 :=
  PSTRTMSeq005.seqMachine (a:=1009) (b:=1016) (pairRow fieldA fieldB memory)
    PA17TMRatArithmeticNativeCache030.mulCacheMachine

def cycleRow (fieldA fieldB : SourceField) (memory : Nat) : Machine 2078 :=
  PSTRTMSeq005.seqMachine (a:=2026) (b:=51) (pairNativeRow fieldA fieldB memory)
    (returnHomeMachine 0)

def cycleRowPort : Fin 2079 := PSTRTMSeq005.rightLabel (a:=2026) (homePort 0)

def cycleFamily (p : Nat) (fieldA fieldB : SourceField) (memory : Fin (p+1)) : Machine 2078 :=
  cycleRow fieldA fieldB memory.val

def cyclePorts (p : Nat) (_memory : Fin (p+1)) (_local : Fin 2079) :
    Option (Fin (p+1) × Fin 2079) := none

def cycleCap (p : Nat) : Nat := totalStates p 2078
attribute [local implicit_reducible] cycleCap totalStates

def cycleMachine (p : Nat) (fieldA fieldB : SourceField) : Machine (cycleCap p) :=
  blockMachine (cycleFamily p fieldA fieldB) (cyclePorts p)

def cycleEntry (p : Nat) (memory : Fin (p+1)) : Fin (cycleCap p+1) :=
  label memory (0 : Fin 2079)

def cyclePort (p : Nat) (memory : Fin (p+1)) : Fin (cycleCap p+1) :=
  label memory cycleRowPort

def cacheRecord (gap value : Nat) : RecordSpec := ⟨gap,PSTRTMNatValue017.rawPayload value⟩

def cycleOutput (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (newGap value : Nat) : Tape Bool :=
  homeOutput sx counter (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)
    (cacheRecord newGap value) [] []

def cycleFee (fieldA fieldB : SourceField) (memory : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) (gap newGap a b : Nat) : Nat :=
  pairFee fieldA fieldB memory nxTail dxTail nyTail dyTail gap a b+
    65536*(PA17TMRatArithmeticNativeCache030.scale a b)^2+
    (newGap+2*natBits (a*b)+2*PA17TMRatArithmeticFarLoad031.bankWidth nxTail dxTail nyTail dyTail+49)

theorem cycleRowPort_value : cycleRowPort.val=2078 := by decide

theorem cycleCap_eq (p : Nat) : cycleCap p=2079*p+2078 := by
  simp only [cycleCap,totalStates]
  omega

theorem cycleEntry_value (p : Nat) (memory : Fin (p+1)) :
    (cycleEntry p memory).val=2079*memory.val := by
  simp only [cycleEntry,label,Fin.val_zero,Nat.add_zero,Nat.mul_comm]

theorem cyclePort_value (p : Nat) (memory : Fin (p+1)) :
    (cyclePort p memory).val=2079*memory.val+2078 := by
  simp only [cyclePort,label,cycleRowPort_value,Nat.mul_comm]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstMul051
