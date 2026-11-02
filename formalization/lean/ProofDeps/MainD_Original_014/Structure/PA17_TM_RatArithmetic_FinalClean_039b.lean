module
public import Structure.PA17_TM_RatArithmetic_FinalClean_039a

/-! Actually erase all caches, restore the actual FALSE source footer, then
use the frozen real source rewind. Source fields remain intact until035. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFinalClean039

open Turing
open PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticEraseBank034
open PA17TMRatArithmeticAllocate013

def cacheSpan (j : Nat) (first : RecordSpec) (later : List RecordSpec) : Nat :=
  cacheGap first later+2*cacheWidth first later+5*(j+1)

def cachesErasedCap (j : Nat) : Nat := latestCap j+eraseCap (j+1)+1
def reclampedCap (j : Nat) : Nat := cachesErasedCap j+1+1
def headerCap (j : Nat) : Nat := reclampedCap j+34+1

attribute [local implicit_reducible] cachesErasedCap reclampedCap headerCap

def eraseCachesMachine (j : Nat) : Machine (cachesErasedCap j) :=
  PSTRTMSeq005.seqMachine (seekLatestMachine j) (eraseBankMachine (j+1))
def reclampFooterMachine (j : Nat) : Machine (reclampedCap j) :=
  PSTRTMSeq005.seqMachine (eraseCachesMachine j) (setMarkerMachine false)
def backHeaderMachine (j : Nat) : Machine (headerCap j) :=
  PSTRTMSeq005.seqMachine (reclampFooterMachine j) finishBackMachine

def headerPort (j : Nat) : Fin (headerCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=reclampedCap j) (34 : Fin 35)

def clearedHeaderTape (j : Nat) (first : RecordSpec) (later : List RecordSpec) (sx : Bool)
    (nx dxTail ny dyTail suffix : List Bool) : Tape Bool :=
  Tape.mk₂ [false] (prefixRight sx (bank nx (false::dxTail) ny (false::dyTail)
    (List.replicate (cacheSpan j first later) false++suffix)))

/-- All cache markers/data/flags/END00 are genuinely FALSE now. Actual
WRITE_FALSE restored the original footer before the actual finishBack route. -/
theorem backHeader_bounded (j : Nat) (first : RecordSpec) (later : List RecordSpec)
    (hj : later.length=j) (sx : Bool) (nx dxTail ny dyTail suffix : List Bool) :
    BoundedRun (s:=headerCap j) (backHeaderMachine j)
      (residentInput sx nx dxTail ny dyTail first later suffix) (headerPort j)
      (clearedHeaderTape j first later sx nx dxTail ny dyTail suffix)
      (3*cacheGap first later+12*cacheWidth first later+49*j+2*sourceWidth nx dxTail ny dyTail+92) := by
  have hs := seekLatest_bounded j first later hj sx nx dxTail ny dyTail suffix
  have hn : (first::later).length=j+1 := by simp only [List.length_cons,hj]
  have he := eraseBank_bounded (j+1) (first::later) hn (sourceFooterLeft sx nx dxTail ny dyTail) suffix
  have hm : BoundedRun (s:=1) (setMarkerMachine false)
      (Tape.mk₂ (sourceFooterLeft sx nx dxTail ny dyTail)
        (true::(List.replicate (cacheSpan j first later) false++suffix))) 1
      (Tape.mk₂ (sourceFooterLeft sx nx dxTail ny dyTail)
        (false::(List.replicate (cacheSpan j first later) false++suffix))) 2 :=
    ⟨setMarkerTrace true false (sourceFooterLeft sx nx dxTail ny dyTail)
       (List.replicate (cacheSpan j first later) false++suffix),
     setMarker_runsFrom true false (sourceFooterLeft sx nx dxTail ny dyTail)
       (List.replicate (cacheSpan j first later) false++suffix),by rfl⟩
  have hf := finishBack_bounded sx [false] nx (false::dxTail) ny (false::dyTail)
    (List.replicate (cacheSpan j first later) false++suffix)
  have h := ((hs.seq he).seq hm).seq hf
  apply h.mono
  simp only [cacheGap,cacheWidth,sourceWidth]
  omega

theorem clearedHeader_gap (j : Nat) (first : RecordSpec) (later : List RecordSpec) (sx : Bool)
    (nx dxTail ny dyTail : List Bool) (gap : Nat) (word : List Bool) :
    clearedHeaderTape j first later sx nx dxTail ny dyTail (List.replicate gap false++true::word) =
      Tape.mk₂ [false] (prefixRight sx (bank nx (false::dxTail) ny (false::dyTail)
        (List.replicate (cacheSpan j first later+gap) false++true::word))) := by
  have ht : List.replicate (cacheSpan j first later) false++(List.replicate gap false++true::word) =
      List.replicate (cacheSpan j first later+gap) false++true::word := by
    calc
      _ = (List.replicate (cacheSpan j first later) false++List.replicate gap false)++true::word :=
        (List.append_assoc _ _ _).symm
      _ = _ := congrArg (fun bits : List Bool => bits++true::word)
        (List.replicate_add (cacheSpan j first later) gap false).symm
  unfold clearedHeaderTape
  rw [ht]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFinalClean039
