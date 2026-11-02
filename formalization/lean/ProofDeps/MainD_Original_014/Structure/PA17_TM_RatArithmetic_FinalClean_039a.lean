module
public import Structure.PA17_TM_RatArithmetic_ReturnHome_037b
public import Structure.PA17_TM_RatArithmetic_EraseBank_034c
public import Structure.PA17_TM_RatArithmetic_Allocate_013e

/-! Reach the REAL original FALSE footer, physically write TRUE, then use
the frozen forward walk to the latest end. The initial FALSE is not assumed
to be TRUE and the original source bank remains intact throughout. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFinalClean039

open Turing
open PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticReturnHome037
open PA17TMRatArithmeticAllocate013

def cacheGap (first : RecordSpec) (later : List RecordSpec) : Nat := totalGap (first::later)
def cacheWidth (first : RecordSpec) (later : List RecordSpec) : Nat := totalWidth (first::later)
def sourceWidth (nx dxTail ny dyTail : List Bool) : Nat := bankWidth nx (false::dxTail) ny (false::dyTail)

def sourceFooterLeft (sx : Bool) (nx dxTail ny dyTail : List Bool) : List Bool :=
  footerLeft sx [false] nx (false::dxTail) ny (false::dyTail)

def residentInput (sx : Bool) (nx dxTail ny dyTail : List Bool) (first : RecordSpec)
    (later : List RecordSpec) (suffix : List Bool) : Tape Bool :=
  homeInput sx [false] nx (false::dxTail) ny (false::dyTail) first later suffix

def footerPort (j : Nat) : Fin (firstCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=backwardCap j) (15 : Fin 16)

theorem toFooter_bounded (j : Nat) (first : RecordSpec) (later : List RecordSpec)
    (hj : later.length=j) (sx : Bool) (nx dxTail ny dyTail suffix : List Bool) :
    BoundedRun (s:=firstCap j) (toFirstMachine j) (residentInput sx nx dxTail ny dyTail first later suffix)
      (footerPort j) (Tape.mk₂ (sourceFooterLeft sx nx dxTail ny dyTail)
        (false::bankTail (first::later) suffix))
      (cacheGap first later+2*cacheWidth first later+12*j+18) := by
  have hb := backward_bounded j later hj (firstLeft sx [false] nx (false::dxTail) ny (false::dyTail) first) suffix
  have ho := firstFooter_bounded sx [false] nx (false::dxTail) ny dyTail first (bankTail later suffix)
  have h := hb.seq ho
  apply h.mono
  simp only [cacheGap,cacheWidth,totalGap,totalWidth]
  omega

def markedCap (j : Nat) : Nat := firstCap j+1+1
def latestCap (j : Nat) : Nat := markedCap j+forwardCap (j+1)+1

attribute [local implicit_reducible] markedCap latestCap

def markFooterMachine (j : Nat) : Machine (markedCap j) :=
  PSTRTMSeq005.seqMachine (toFirstMachine j) (setMarkerMachine true)

def seekLatestMachine (j : Nat) : Machine (latestCap j) :=
  PSTRTMSeq005.seqMachine (markFooterMachine j) (forwardMachine (j+1))

def latestPort (j : Nat) : Fin (latestCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=markedCap j) (forwardPort (j+1))

/-- The old footer is now TRUE because an actual WRITE executed there.
Every original source byte is otherwise unchanged; all caches/suffix survive. -/
theorem seekLatest_bounded (j : Nat) (first : RecordSpec) (later : List RecordSpec)
    (hj : later.length=j) (sx : Bool) (nx dxTail ny dyTail suffix : List Bool) :
    BoundedRun (s:=latestCap j) (seekLatestMachine j)
      (residentInput sx nx dxTail ny dyTail first later suffix) (latestPort j)
      (bankEnd (sourceFooterLeft sx nx dxTail ny dyTail) (first::later) suffix)
      (2*cacheGap first later+4*cacheWidth first later+21*j+30) := by
  have ht := toFooter_bounded j first later hj sx nx dxTail ny dyTail suffix
  have hm : BoundedRun (s:=1) (setMarkerMachine true)
      (Tape.mk₂ (sourceFooterLeft sx nx dxTail ny dyTail) (false::bankTail (first::later) suffix)) 1
      (bankStart (sourceFooterLeft sx nx dxTail ny dyTail) (first::later) suffix) 2 :=
    ⟨setMarkerTrace false true (sourceFooterLeft sx nx dxTail ny dyTail) (bankTail (first::later) suffix),
     setMarker_runsFrom false true (sourceFooterLeft sx nx dxTail ny dyTail) (bankTail (first::later) suffix),by rfl⟩
  have hn : (first::later).length=j+1 := by simp only [List.length_cons,hj]
  have hf := forward_bounded (j+1) (first::later) hn (sourceFooterLeft sx nx dxTail ny dyTail) suffix
  have h := (ht.seq hm).seq hf
  apply h.mono
  simp only [cacheGap,cacheWidth]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFinalClean039
