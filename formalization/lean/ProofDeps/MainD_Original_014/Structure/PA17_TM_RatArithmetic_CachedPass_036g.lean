module
public import Structure.PA17_TM_RatArithmetic_CachedPass_036f

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
open PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticAllocatePass023

def cachedFieldCap (j k : Nat) : Nat := sourceLoopCap (cachedCycleCap j k)
attribute [local implicit_reducible] sourceLoopCap cachedCycleCap cachedFieldCap

def cachedFieldMachine (j k : Nat) (out back : Machine 26) : Machine (cachedFieldCap j k) :=
  sourceLoopMachine (cachedCycleCap j k) (cachedCycleCap_ge j k) (cachedCycleMachine j k out back)
def cachedFieldExit (j k : Nat) : Fin (cachedFieldCap j k+1) :=
  sourceExit (cachedCycleCap j k) (cachedCycleCap_ge j k)

def cachedFieldFee (j k : Nat) (records : List RecordSpec) (n width following : Nat) : Nat :=
  width*(2*n+(2*k+4)*width+4*k+cycleSurcharge j records following+4)+2

theorem cached_field_bounded (j k : Nat) (out back : Machine 26) (outPort backPort : Fin 27)
    (rest : List Bool → List Bool) (footer : List Bool → List Bool → List Bool) (following : Nat)
    (routes : FramedSourceRoutes out back outPort backPort rest footer following)
    (records : List RecordSpec) (hj : records.length=j) (left digits : List Bool) (n : Nat) :
    BoundedRun (s:=cachedFieldCap j k) (cachedFieldMachine j k out back)
      (Turing.Tape.mk₂ left (nxStream digits (false::rest (bankTail records (gapWord n)))))
      (cachedFieldExit j k)
      (Turing.Tape.mk₂ (pushField left digits)
        (false::rest (bankTail records (gapWord (n+k*digits.length)))))
      (cachedFieldFee j k records n digits.length following) :=
  source_foreach_bounded (cachedCycleCap j k) (cachedCycleCap_ge j k) (cachedCycleMachine j k out back)
    k (cycleSurcharge j records following) (fun n => rest (bankTail records (gapWord n)))
    (cached_cycle_contract j k out back outPort backPort rest footer following routes records hj) left digits n

theorem cachedFieldCap_eq (j k : Nat) : cachedFieldCap j k=30*k+44*j+155 := by
  unfold cachedFieldCap sourceLoopCap totalStates
  simp only [cachedCycleCap_eq]
  omega

def nxCachedFieldMachine (j k : Nat) : Machine (cachedFieldCap j k) := cachedFieldMachine j k outNxCode returnNxCode
def dxCachedFieldMachine (j k : Nat) : Machine (cachedFieldCap j k) := cachedFieldMachine j k outDxCode returnDxCode
def nyCachedFieldMachine (j k : Nat) : Machine (cachedFieldCap j k) := cachedFieldMachine j k outNyCode returnNyCode
def dyCachedFieldMachine (j k : Nat) : Machine (cachedFieldCap j k) := cachedFieldMachine j k outDyCode returnDyCode

def firstCachedCap (j k : Nat) : Nat := cachedFieldCap j k+cachedFieldCap j k+1
def headerCachedCap (j k : Nat) : Nat := firstCachedCap j k+2+1
def thirdCachedCap (j k : Nat) : Nat := headerCachedCap j k+cachedFieldCap j k+1
def fourCachedCap (j k : Nat) : Nat := thirdCachedCap j k+cachedFieldCap j k+1
def rawCachedPassCap (j k : Nat) : Nat := fourCachedCap j k+34+1
def cachedPassCap (j k : Nat) : Nat := 120*k+176*j+661

def firstCachedMachine (j k : Nat) : Machine (firstCachedCap j k) :=
  PSTRTMSeq005.seqMachine (nxCachedFieldMachine j k) (dxCachedFieldMachine j k)
def headerCachedMachine (j k : Nat) : Machine (headerCachedCap j k) :=
  PSTRTMSeq005.seqMachine (firstCachedMachine j k) headerRightMachine
def thirdCachedMachine (j k : Nat) : Machine (thirdCachedCap j k) :=
  PSTRTMSeq005.seqMachine (headerCachedMachine j k) (nyCachedFieldMachine j k)
def fourCachedMachine (j k : Nat) : Machine (fourCachedCap j k) :=
  PSTRTMSeq005.seqMachine (thirdCachedMachine j k) (dyCachedFieldMachine j k)
def rawCachedPassMachine (j k : Nat) : Machine (rawCachedPassCap j k) :=
  PSTRTMSeq005.seqMachine (fourCachedMachine j k) finishBackMachine

theorem rawCachedPassCap_eq (j k : Nat) : rawCachedPassCap j k=cachedPassCap j k := by
  unfold rawCachedPassCap fourCachedCap thirdCachedCap headerCachedCap firstCachedCap cachedPassCap
  simp only [cachedFieldCap_eq]
  omega

/-- Static equal-cap label reindexing; the program is fixed by j/k before
all source bits, cache records, counter values and gap lengths. -/
def cachedPassMachine (j k : Nat) : Machine (cachedPassCap j k) :=
  padMachine (Nat.le_of_eq (rawCachedPassCap_eq j k)) (rawCachedPassMachine j k)

def cachedPassFee (j k : Nat) (records : List RecordSpec) (width n : Nat) : Nat :=
  width*(2*n+(2*k+4)*width+4*k+2*totalGap records+4*totalWidth records+21*j+74)+48

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
