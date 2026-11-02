module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038k

/-! A plain cached-source copy body after real observation. Only fixed-j
code is used: paid OWN initialization, SAME042 loop, then paid SOURCE and
DEST LSB restoration. The following module supplies the actual read branch. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticAllocatePass023 (pushField)

theorem flagged_cons (bit : Bool) (tail : List Bool) :
    PSTRTMIncrement009.blocks (bit::tail)=bit::true::PSTRTMIncrement009.blocks tail := by
  simp only [PSTRTMIncrement009.blocks,List.flatMap_cons,List.cons_append,List.nil_append]

def cachedPlainBodyCap (j : Nat) : Nat :=
  plainBeforeCap (cachedOutCap j) (cachedBackCap j)+cachedDoneCap j+1
def cachedPlainBodyMachine (phase : Fin 2) (j : Nat) : Machine (cachedPlainBodyCap j) :=
  PSTRTMSeq005.seqMachine (a:=plainBeforeCap (cachedOutCap j) (cachedBackCap j)) (b:=cachedDoneCap j)
    (plainBeforeMachine (cachedRoute j)) (cachedDoneRow (p:=0) phase j .plain)
def cachedPlainBodyPort (j : Nat) : Fin (cachedPlainBodyCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=plainBeforeCap (cachedOutCap j) (cachedBackCap j)) (cachedDonePort j)
def cachedPlainBodyFee (j : Nat) (records : List RecordSpec) (tail : List Bool) (gap : Nat) : Nat :=
  ((4*(false::tail).length+2*cachedCost j records+2*gap+19)+
    PA17TMRatArithmeticCopyLoop042.loopFee (plainLoopFee (cachedCost j records) gap) [] (false::tail))+
    cachedDoneFee j .plain records (false::tail).length 0 gap

theorem cached_plain_body_bounded (phase : Fin 2) (j : Nat) (records : List RecordSpec)
    (hj : records.length=j) (archive tail : List Bool) (gap : Nat) :
    BoundedRun (cachedPlainBodyMachine phase j)
      (Tape.mk₂ (false::archive) (cachedWord records (false::tail) (plainWorkSuffix gap []))) (cachedPlainBodyPort j)
      (Tape.mk₂ (destinationLeft .plain (cachedFinish records (false::archive) (seenBit (p:=0) phase::tail)) [] gap true)
        (PA17TMRatArithmeticCopy006.workspace (seenBit (p:=0) phase::tail)))
      (cachedPlainBodyFee j records tail gap) := by
  have hb := plain_before_bounded (cachedRoute j) (cacheContext records) (cachedFinish records)
    (cachedCost j records) gap archive (false::tail) (cached_correct j records hj) rfl
  have hd := cached_done_row_bounded (p:=0) phase j records hj .plain archive tail [] [] gap
  simp only [List.append_nil,List.length_nil] at hd
  have before : BoundedRun (plainBeforeMachine (cachedRoute j))
      (Tape.mk₂ (false::archive) (cachedWord records (false::tail) (plainWorkSuffix gap [])))
      (plainBeforePort (cachedOutCap j) (cachedBackCap j))
      (Tape.mk₂ (pushField (false::archive) (false::tail))
        (cacheContext records++true::destinationSuffix .plain [] (copiedTail tail []) gap))
      ((4*(false::tail).length+2*cachedCost j records+2*gap+19)+
        PA17TMRatArithmeticCopyLoop042.loopFee (plainLoopFee (cachedCost j records) gap) [] (false::tail)) := by
    simpa only [passedLeft_blocks,pushField,cachedWord,cachedRoute,
      PA17TMRatArithmeticPairExcursion041.sourceWord,plainWorkSuffix,
      PA17TMRatArithmeticFarLoad031.workSuffix,destinationSuffix,destinationWord,
      copiedTail,PA17TMRatArithmeticCopy006.workspace,flagged_cons,List.cons_append,List.append_nil] using hb
  simpa only [cachedPlainBodyMachine,cachedPlainBodyCap,cachedPlainBodyPort,cachedPlainBodyFee,
    PA17TMRatArithmeticCopy006.workspace] using before.seq hd

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
