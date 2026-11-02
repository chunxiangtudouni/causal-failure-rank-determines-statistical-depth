module
public import Structure.PA17_TM_RatArithmetic_FinalClean_039b
public import Structure.PA17_TM_RatArithmetic_ClearInput_035e

/-! Whole cache plus original-source cleanup. The output is already present
on an actual intermediate Tape; no answer is supplied to the original input
or executable program. The caller must first prove its real output producer. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFinalClean039

open Turing
open PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticEraseBank034

def finalCap (j : Nat) : Nat := headerCap j+38+1
attribute [local implicit_reducible] finalCap

/-- j is compiled before all original inputs/source/cache/output values.
It counts later records after a mandatory first cache (total j+1). -/
def finalCleanMachine (j : Nat) : Machine (finalCap j) :=
  PSTRTMSeq005.seqMachine (backHeaderMachine j) PA17TMRatArithmeticClearInput035.clearAndReturnMachine

def finalPort (j : Nat) : Fin (finalCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=headerCap j) (38 : Fin 39)

theorem finalCap_eq (j : Nat) : finalCap j=48*j+131 := by
  simp only [finalCap,headerCap,reclampedCap,cachesErasedCap,latestCap,markedCap,
    PA17TMRatArithmeticReturnHome037.firstCap,backwardCap_eq,forwardCap_eq,eraseCap_eq]
  omega

theorem finalClean_bounded (j : Nat) (first : RecordSpec) (later : List RecordSpec)
    (hj : later.length=j) (sx : Bool) (nx dxTail ny dyTail : List Bool) (gap : Nat) (word : List Bool) :
    BoundedRun (s:=finalCap j) (finalCleanMachine j)
      (residentInput sx nx dxTail ny dyTail first later (List.replicate gap false++true::word)) (finalPort j)
      (Tape.mk₁ (true::word))
      (4*cacheGap first later+14*cacheWidth first later+54*j+10*sourceWidth nx dxTail ny dyTail+gap+157) := by
  have hh := backHeader_bounded j first later hj sx nx dxTail ny dyTail (List.replicate gap false++true::word)
  rw [clearedHeader_gap] at hh
  obtain ⟨trace,hr,hl,_⟩ := PA17TMRatArithmeticClearInput035.clear_standalone_contract sx nx dxTail ny dyTail
    (cacheSpan j first later+gap) word
  have hc : BoundedRun (s:=38) PA17TMRatArithmeticClearInput035.clearAndReturnMachine
      (Tape.mk₂ [false] (prefixRight sx (bank nx (false::dxTail) ny (false::dyTail)
        (List.replicate (cacheSpan j first later+gap) false++true::word)))) 38
      (Tape.mk₁ (true::word))
      (8*sourceWidth nx dxTail ny dyTail+(cacheSpan j first later+gap)+60) := ⟨trace,hr,hl⟩
  have h := hh.seq hc
  apply h.mono
  simp only [cacheSpan]
  omega

/-- ONE actual trace erases every cached record and the original bank,
physically reaches the already-produced output and HALTs on its TRUE header.
All remaining Tape is exactly that output, including its arbitrary suffix. -/
theorem finalClean_contract (j : Nat) (first : RecordSpec) (later : List RecordSpec)
    (hj : later.length=j) (sx : Bool) (nx dxTail ny dyTail : List Bool) (gap : Nat) (word : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (finalCleanMachine j)
        ⟨0,residentInput sx nx dxTail ny dyTail first later (List.replicate gap false++true::word)⟩ trace
        ⟨finalPort j,Tape.mk₁ (true::word)⟩ ∧
      trace.length≤4*cacheGap first later+14*cacheWidth first later+54*j+
        10*sourceWidth nx dxTail ny dyTail+gap+157 ∧
      ∀ prefixLength chargedL, visitedSpace (finalCleanMachine j) chargedL (trace.take prefixLength) ≤
        chargedL+8*cacheGap first later+28*cacheWidth first later+108*j+
          20*sourceWidth nx dxTail ny dyTail+2*gap+315 := by
  obtain ⟨trace,hr,hl⟩ := finalClean_bounded j first later hj sx nx dxTail ny dyTail gap word
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le (finalCleanMachine j) chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFinalClean039
