module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031k
public import Structure.PA17_TM_RatArithmetic_WorkHome_046a
public import Structure.PA17_TM_RatArithmetic_Mul_047c
public import Structure.PA17_TM_RatArithmetic_PairEncode_017c
public import Structure.PA17_TM_RatArithmetic_SignRead_021b

/-! Real original-source A/B input construction. Code depends only on
fixed field choices and finite row bound p. Actual row, width, gap and
canonical values are poststate metadata, never extra original input. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairInput050

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticMul047
attribute [local implicit_reducible] sharedLoopCap sharedBeforeCap sharedCopyCap

def restoredDigits (field : SourceField) (memory : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) : List Bool :=
  memory.testBit (sourceSlot field)::sourceTail field nxTail dxTail nyTail dyTail

def firstRow (field : SourceField) (memory : Nat) : Machine 478 :=
  PSTRTMSeq005.seqMachine (a:=435) (b:=42)
    (restoreRowMachine (sourceNavigation field) (sourceRoute field) (sourceSlot field) memory)
    PA17TMRatArithmeticWorkHome046.originalHomeMachine

def secondRoute (field : SourceField) : PA17TMRatArithmeticPairExcursion041.SourceRoute 10 26 :=
  PA17TMRatArithmeticPairExcursion041.originalRoute (sourceRoute field)

def secondCopyRow (field : SourceField) : Machine 480 :=
  PSTRTMSeq005.seqMachine (a:=16) (b:=463) (sourceNavigation field)
    (sharedCopyMachine (secondRoute field))

def secondRow (field : SourceField) (memory : Nat) : Machine 482 :=
  PSTRTMSeq005.seqMachine (a:=480) (b:=1) (secondCopyRow field)
    (PA17TMRatArithmeticAllocate013.setMarkerMachine (memory.testBit (sourceSlot field)))

def bothRow (fieldA fieldB : SourceField) (memory : Nat) : Machine 961 :=
  PSTRTMSeq005.seqMachine (a:=478) (b:=482) (firstRow fieldA memory) (secondRow fieldB memory)

def pairRow (fieldA fieldB : SourceField) (memory : Nat) : Machine 1009 :=
  PSTRTMSeq005.seqMachine (a:=961) (b:=47) (bothRow fieldA fieldB memory)
    PA17TMRatArithmeticPairEncode017.plainMachine

def pairFamily (p : Nat) (fieldA fieldB : SourceField) (memory : Fin (p+1)) : Machine 1009 :=
  pairRow fieldA fieldB memory.val

def pairPorts (p : Nat) (_memory : Fin (p+1)) (_local : Fin 1010) :
    Option (Fin (p+1) × Fin 1010) := none

def pairCap (p : Nat) : Nat := totalStates p 1009
attribute [local implicit_reducible] pairCap totalStates

/-- All rows are compiled before all x/y. A real prior control transfer
must enter pairEntry p memory; no host selects code by saved operand bits. -/
def pairInputMachine (p : Nat) (fieldA fieldB : SourceField) : Machine (pairCap p) :=
  blockMachine (pairFamily p fieldA fieldB) (pairPorts p)

def pairEntry (p : Nat) (memory : Fin (p+1)) : Fin (pairCap p+1) := label memory (0 : Fin 1010)
def pairPort (p : Nat) (memory : Fin (p+1)) : Fin (pairCap p+1) := label memory (1009 : Fin 1010)

def pairArchive (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) : List Bool :=
  true::(List.replicate gap false++false::globalSourceLeft sx counter nxTail dxTail nyTail dyTail)

def nativeInputTape (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (gap a b : Nat) : Tape Bool :=
  Tape.mk₂ (false::pairArchive sx counter nxTail dxTail nyTail dyTail gap) (encodeNat a++encodeNat b)

def firstFee (field : SourceField) (nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) : Nat :=
  navigationFee nxTail dxTail nyTail+
    copyFee (false::sourceTail field nxTail dxTail nyTail dyTail)
      (sourceCost field dxTail nyTail dyTail) gap+2+
    (gap+2*PA17TMRatArithmeticFarLoad031.bankWidth nxTail dxTail nyTail dyTail+41)

def secondFee (field : SourceField) (nxTail dxTail nyTail dyTail first : List Bool) (gap : Nat) : Nat :=
  navigationFee nxTail dxTail nyTail+
    sharedCopyFee (false::sourceTail field nxTail dxTail nyTail dyTail) first
      (sourceCost field dxTail nyTail dyTail) gap+2

def pairFee (fieldA fieldB : SourceField) (memory : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat) : Nat :=
  firstFee fieldA nxTail dxTail nyTail dyTail gap+
    secondFee fieldB nxTail dxTail nyTail dyTail
      (restoredDigits fieldA memory nxTail dxTail nyTail dyTail) gap+
    64*((PA17TMRatArithmeticPairEncode017.payload a).length+
      (PA17TMRatArithmeticPairEncode017.payload b).length+1)^2

theorem pairCap_eq (p : Nat) : pairCap p=1010*p+1009 := by
  simp only [pairCap,totalStates]
  omega

theorem pairEntry_value (p : Nat) (memory : Fin (p+1)) : (pairEntry p memory).val=1010*memory.val := by
  simp only [pairEntry,label,Fin.val_zero,Nat.add_zero,Nat.mul_comm]

theorem pairPort_value (p : Nat) (memory : Fin (p+1)) : (pairPort p memory).val=1010*memory.val+1009 := by
  have hq : (1009 : Fin 1010).val=1009 := by decide
  simp only [pairPort,label,hq,Nat.mul_comm]

theorem original_source_route_correct (field : SourceField) (dxTail nyTail dyTail : List Bool) :
    PA17TMRatArithmeticPairExcursion041.SourceCorrect (secondRoute field)
      (sourceContext field dxTail nyTail dyTail) (sourceFinish field dxTail nyTail dyTail)
      (sourceCost field dxTail nyTail dyTail) :=
  PA17TMRatArithmeticPairExcursion041.original_correct _ _ _ _
    (source_correct field dxTail nyTail dyTail)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairInput050
