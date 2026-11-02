module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038n
public import Structure.PA17_TM_RatArithmetic_Mul_047c

/-! Shared-B cached-source body, using the frozen047 initialization and
SAME042 copy loop. Only the paid cached EOF/source/DEST hook is appended. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticAllocatePass023 (pushField)

def cachedSharedBodyCap (j : Nat) : Nat :=
  PA17TMRatArithmeticMul047.sharedBeforeCap (cachedOutCap j) (cachedBackCap j)+cachedDoneCap j+1
def cachedSharedBodyMachine (phase : Fin 2) (j : Nat) : Machine (cachedSharedBodyCap j) :=
  PSTRTMSeq005.seqMachine (a:=PA17TMRatArithmeticMul047.sharedBeforeCap (cachedOutCap j) (cachedBackCap j))
    (b:=cachedDoneCap j) (PA17TMRatArithmeticMul047.sharedBeforeMachine (cachedRoute j))
    (cachedDoneRow (p:=0) phase j .shared)
def cachedSharedBodyPort (j : Nat) : Fin (cachedSharedBodyCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=PA17TMRatArithmeticMul047.sharedBeforeCap (cachedOutCap j) (cachedBackCap j))
    (cachedDonePort j)
def cachedSharedBodyFee (j : Nat) (records : List RecordSpec) (tail a : List Bool) (gap : Nat) : Nat :=
  ((4*(false::tail).length+2*cachedCost j records+2*gap+4*a.length+30)+
    PA17TMRatArithmeticCopyLoop042.loopFee
      (PA17TMRatArithmeticMul047.sharedFee (cachedCost j records) gap a) [] (false::tail))+
    cachedDoneFee j .shared records (false::tail).length a.length gap

theorem cached_shared_body_bounded (phase : Fin 2) (j : Nat) (records : List RecordSpec)
    (hj : records.length=j) (archive tail a : List Bool) (gap : Nat) :
    BoundedRun (cachedSharedBodyMachine phase j)
      (Tape.mk₂ (false::archive) (cachedWord records (false::tail)
        (PA17TMRatArithmeticPairExcursion041.workSuffix gap a []))) (cachedSharedBodyPort j)
      (Tape.mk₂ (destinationLeft .shared (cachedFinish records (false::archive) (seenBit (p:=0) phase::tail)) a gap true)
        (PA17TMRatArithmeticCopy006.workspace (seenBit (p:=0) phase::tail)))
      (cachedSharedBodyFee j records tail a gap) := by
  have hb := PA17TMRatArithmeticMul047.shared_before_bounded (cachedRoute j) (cacheContext records)
    (cachedFinish records) (cachedCost j records) gap archive (false::tail) a (cached_correct j records hj) rfl
  have hd := cached_done_row_bounded (p:=0) phase j records hj .shared archive tail a [] gap
  simp only [List.append_nil] at hd
  have before : BoundedRun (PA17TMRatArithmeticMul047.sharedBeforeMachine (cachedRoute j))
      (Tape.mk₂ (false::archive) (cachedWord records (false::tail)
        (PA17TMRatArithmeticPairExcursion041.workSuffix gap a [])))
      (PA17TMRatArithmeticMul047.sharedBeforePort (cachedOutCap j) (cachedBackCap j))
      (Tape.mk₂ (pushField (false::archive) (false::tail))
        (cacheContext records++true::destinationSuffix .shared a (copiedTail tail []) gap))
      ((4*(false::tail).length+2*cachedCost j records+2*gap+4*a.length+30)+
        PA17TMRatArithmeticCopyLoop042.loopFee
          (PA17TMRatArithmeticMul047.sharedFee (cachedCost j records) gap a) [] (false::tail)) := by
    simpa only [passedLeft_blocks,pushField,cachedWord,cachedRoute,
      PA17TMRatArithmeticPairExcursion041.sourceWord,PA17TMRatArithmeticPairExcursion041.workSuffix,
      destinationSuffix,destinationWord,copiedTail,PA17TMRatArithmeticCopy006.workspace,
      flagged_cons,List.cons_append,List.append_nil] using hb
  simpa only [cachedSharedBodyMachine,cachedSharedBodyCap,cachedSharedBodyPort,cachedSharedBodyFee,
    PA17TMRatArithmeticCopy006.workspace] using before.seq hd

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
