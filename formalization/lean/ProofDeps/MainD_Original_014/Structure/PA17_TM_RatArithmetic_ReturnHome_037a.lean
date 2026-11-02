module
public import Structure.PA17_TM_RatArithmetic_BankWalk_033b
public import Structure.PA17_TM_RatArithmetic_Width_018i

/-! Latest cache end to original header. The first cache really follows a
FALSE original footer; only the later caches use TRUE old-marker navigation. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticReturnHome037

open Turing
open PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticRecordNav032
open PA17TMRatArithmeticBankWalk033

def footerLeft (sx : Bool) (counter nx dx ny dy : List Bool) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks dy.reverse++false::dyContext sx counter nx dx ny)

def firstLeft (sx : Bool) (counter nx dx ny dy : List Bool) (first : RecordSpec) : List Bool :=
  recordLeft first.gap (footerLeft sx counter nx dx ny dy) false first.digits

def homeInput (sx : Bool) (counter nx dx ny dy : List Bool) (first : RecordSpec)
    (later : List RecordSpec) (suffix : List Bool) : Tape Bool :=
  bankEnd (firstLeft sx counter nx dx ny dy first) later suffix

def homeOutput (sx : Bool) (counter nx dx ny dy : List Bool) (first : RecordSpec)
    (later : List RecordSpec) (suffix : List Bool) : Tape Bool :=
  Tape.mk₂ counter (prefixRight sx (bank nx dx ny dy (bankTail (first::later) suffix)))

def firstCap (j : Nat) : Nat := backwardCap j+15+1
def homeCap (j : Nat) : Nat := firstCap j+34+1

def toFirstMachine (j : Nat) : Machine (firstCap j) :=
  PSTRTMSeq005.seqMachine (backwardMachine j) originalFooterMachine

/-- j is compiled before every original input/cache value. There are j
later records plus ONE first record after the actual FALSE source footer. -/
def returnHomeMachine (j : Nat) : Machine (homeCap j) :=
  PSTRTMSeq005.seqMachine (toFirstMachine j) finishBackMachine

def homePort (j : Nat) : Fin (homeCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=firstCap j) (34 : Fin 35)

/-- Every clamped Dy field is nonempty and its last physical FLAG is
TRUE. END0 is retained, and the originalFooter route really uses two RIGHTs. -/
theorem firstFooter_bounded (sx : Bool) (counter nx dx ny dyTail : List Bool)
    (first : RecordSpec) (suffix : List Bool) :
    BoundedRun (s:=15) originalFooterMachine
      (nextOutput first.gap (footerLeft sx counter nx dx ny (false::dyTail)) false first.digits suffix) 15
      (nextInput first.gap (footerLeft sx counter nx dx ny (false::dyTail)) false first.digits suffix)
      (first.gap+2*first.digits.length+17) := by
  have hne : (false::dyTail).reverse ≠ [] := by
    intro hz
    have hl := congrArg List.length hz
    simp at hl
  cases hr : (false::dyTail).reverse with
  | nil => exact (hne hr).elim
  | cons last rest =>
    let archive := PSTRTMRawNat010.leftBlocks rest++false::dyContext sx counter nx dx ny
    have hleft : footerLeft sx counter nx dx ny (false::dyTail)=originalArchive archive last := by
      simp [footerLeft,hr,PSTRTMRawNat010.leftBlocks,originalArchive,archive]
    have hf := originalFooter_bounded first.gap archive last first.digits suffix
    rw [←hleft] at hf
    exact hf

theorem returnHome_bounded (j : Nat) (first : RecordSpec) (later : List RecordSpec)
    (hj : later.length=j) (sx : Bool) (counter nx dx ny dyTail suffix : List Bool) :
    BoundedRun (s:=homeCap j) (returnHomeMachine j)
      (homeInput sx counter nx dx ny (false::dyTail) first later suffix) (homePort j)
      (homeOutput sx counter nx dx ny (false::dyTail) first later suffix)
      (totalGap (first::later)+2*totalWidth (first::later)+12*j+
        2*bankWidth nx dx ny (false::dyTail)+49) := by
  have hb := backward_bounded j later hj (firstLeft sx counter nx dx ny (false::dyTail) first) suffix
  have ho := firstFooter_bounded sx counter nx dx ny dyTail first (bankTail later suffix)
  have hf := finishBack_bounded sx counter nx dx ny (false::dyTail) (bankTail (first::later) suffix)
  have h := (hb.seq ho).seq hf
  apply h.mono
  simp only [totalGap,totalWidth]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticReturnHome037
