module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038b
public import Structure.PA17_TM_RatArithmetic_BankWalk_033c

/-! Cached-source routes. Every source/cache end stays TRUE; SOURCE OWN
stays FALSE. The actual one-cell step from OWN to sourceEnd precedes the
shared fixed-j record walk. No following record is treated as zero gap. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticAllocatePass023 (pushField)

/-- Everything between SOURCE END and the latest TRUE end marker. -/
def cacheContext : List RecordSpec → List Bool
  | [] => [false]
  | record::later => false::true::(List.replicate record.gap false++true::false::
      (PSTRTMIncrement009.blocks record.digits++false::cacheContext later))

theorem cacheContext_head (records : List RecordSpec) : (cacheContext records).head?=some false := by
  cases records <;> rfl

theorem cacheContext_word (records : List RecordSpec) (suffix : List Bool) :
    cacheContext records++true::suffix=false::true::bankTail records suffix := by
  induction records with
  | nil => rfl
  | cons record later ih =>
    simp only [cacheContext,bankTail,PA17TMRatArithmeticRecordNav032.recordWord,
      List.cons_append,List.append_assoc,ih]

def cachedWord (records : List RecordSpec) (digits suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks digits++false::(cacheContext records++true::suffix)

def cachedFinish (records : List RecordSpec) (left later : List Bool) : List Bool :=
  bankLeft (false::pushField left later) records

theorem cachedFinish_cons (records : List RecordSpec) (left : List Bool) (bit : Bool) (later : List Bool) :
    cachedFinish records (true::bit::left) later=cachedFinish records left (bit::later) := by
  simp only [cachedFinish,PA17TMRatArithmeticFarLoad031.pushField_cons]

def cachedEndMachine : Machine 3 := PSTRTMSeq005.seqMachine (a:=1) (b:=1)
  PA17TMRatArithmeticWidth018.scanMachine PA17TMRatArithmeticParse002.footerMachine

def cachedOutCap (j : Nat) : Nat := 3+forwardCap j+1
def cachedOutMachine (j : Nat) : Machine (cachedOutCap j) :=
  PSTRTMSeq005.seqMachine (a:=3) (b:=forwardCap j) cachedEndMachine (forwardMachine j)
def cachedOutPort (j : Nat) : Fin (cachedOutCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=3) (forwardPort j)

theorem cached_out_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (left later suffix : List Bool) :
    BoundedRun (cachedOutMachine j) (Tape.mk₂ left (cachedWord records later suffix)) (cachedOutPort j)
      (Tape.mk₂ (cachedFinish records left later) (true::suffix))
      (2*later.length+totalGap records+2*totalWidth records+9*j+5) := by
  have hs : BoundedRun PA17TMRatArithmeticWidth018.scanMachine
      (Tape.mk₂ left (PSTRTMIncrement009.blocks later++false::false::true::bankTail records suffix)) 1
      (Tape.mk₂ (pushField left later) (false::true::bankTail records suffix)) (2*later.length+2) :=
    ⟨PA17TMRatArithmeticWidth018.scanTrace left later false (true::bankTail records suffix),
      PA17TMRatArithmeticWidth018.scan_runsFrom left later false (true::bankTail records suffix),
      by rw [PA17TMRatArithmeticWidth018.scanTrace_length]⟩
  have ha : BoundedRun PA17TMRatArithmeticParse002.footerMachine
      (Tape.mk₂ (pushField left later) (false::true::bankTail records suffix)) 1
      (Tape.mk₂ (false::pushField left later) (true::bankTail records suffix)) 2 :=
    ⟨PA17TMRatArithmeticCleanup026.advanceTrace (pushField left later) false (true::bankTail records suffix),
      PA17TMRatArithmeticCleanup026.advance_runsFrom (pushField left later) false (true::bankTail records suffix),by rfl⟩
  have hf := forward_bounded j records hj (false::pushField left later) suffix
  have result := (hs.seq ha).seq hf
  have cost : (2*later.length+2)+2+(totalGap records+2*totalWidth records+9*j+1)≤
      2*later.length+totalGap records+2*totalWidth records+9*j+5 := by omega
  simpa only [cachedOutMachine,cachedOutCap,cachedEndMachine,cachedOutPort,cachedWord,cacheContext_word,
    cachedFinish,bankStart,bankEnd] using result.mono cost

def cachedBackEndCap (j : Nat) : Nat := backwardCap j+1+1
def cachedBackEndMachine (j : Nat) : Machine (cachedBackEndCap j) :=
  PSTRTMSeq005.seqMachine (a:=backwardCap j) (b:=1)
    (backwardMachine j) PA17TMRatArithmeticParse002.backOneMachine
def cachedBackCap (j : Nat) : Nat := cachedBackEndCap j+5+1
def cachedBackMachine (j : Nat) : Machine (cachedBackCap j) :=
  PSTRTMSeq005.seqMachine (a:=cachedBackEndCap j) (b:=5)
    (cachedBackEndMachine j) PA17TMRatArithmeticParse002.fieldBackMachine
def cachedBackPort (j : Nat) : Fin (cachedBackCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=cachedBackEndCap j) (5 : Fin 6)

theorem cached_back_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive later suffix : List Bool) :
    BoundedRun (cachedBackMachine j)
      (Tape.mk₂ (cachedFinish records (false::archive) later) (true::suffix)) (cachedBackPort j)
      (Tape.mk₂ (false::archive) (cachedWord records later suffix))
      (2*later.length+totalGap records+2*totalWidth records+12*j+8) := by
  have hb := backward_bounded j records hj (false::pushField (false::archive) later) suffix
  have hl : BoundedRun PA17TMRatArithmeticParse002.backOneMachine
      (Tape.mk₂ (false::pushField (false::archive) later) (true::bankTail records suffix)) 1
      (Tape.mk₂ (pushField (false::archive) later) (false::true::bankTail records suffix)) 2 :=
    ⟨PA17TMRatArithmeticParse002.backOneTrace (pushField (false::archive) later) false (true::bankTail records suffix),
      PA17TMRatArithmeticParse002.backOne_runsFrom (pushField (false::archive) later) false (true::bankTail records suffix),by rfl⟩
  have hf : BoundedRun PA17TMRatArithmeticParse002.fieldBackMachine
      (Tape.mk₂ (pushField (false::archive) later) (false::true::bankTail records suffix)) 5
      (Tape.mk₂ (false::archive)
        (PSTRTMIncrement009.blocks later++false::false::true::bankTail records suffix)) (2*later.length+5) :=
    ⟨PA17TMRatArithmeticParse002.fieldBackTrace archive later (false::true::bankTail records suffix),
      PA17TMRatArithmeticParse002.fieldBack_runsFrom archive later (false::true::bankTail records suffix),
      by rw [PA17TMRatArithmeticParse002.fieldBackTrace_length]⟩
  have result := (hb.seq hl).seq hf
  have cost : (totalGap records+2*totalWidth records+12*j+1)+2+(2*later.length+5)≤
      2*later.length+totalGap records+2*totalWidth records+12*j+8 := by omega
  simpa only [cachedBackMachine,cachedBackCap,cachedBackEndCap,cachedBackEndMachine,cachedBackPort,cachedWord,cacheContext_word,
    cachedFinish,bankStart,bankEnd] using result.mono cost

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
