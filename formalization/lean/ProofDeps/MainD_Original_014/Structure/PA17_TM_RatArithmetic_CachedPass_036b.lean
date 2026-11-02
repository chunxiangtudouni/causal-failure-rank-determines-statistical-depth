module
public import Structure.PA17_TM_RatArithmetic_CachedPass_036a

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankWalk033.forwardCap
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankWalk033.backwardCap
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036

open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticAllocate013 (setMarkerMachine setMarkerTrace setMarker_runsFrom)

def markerForwardCap (j : Nat) : Nat := 1+forwardCap j+1
def initSeedCap (j : Nat) : Nat := markerForwardCap j+6+1
def initBackCap (j : Nat) : Nat := initSeedCap j+backwardCap j+1
def bankInitCap (j : Nat) : Nat := initBackCap j+1+1
attribute [local implicit_reducible] markerForwardCap initSeedCap initBackCap bankInitCap

def markerForwardMachine (j : Nat) : Machine (markerForwardCap j) :=
  PSTRTMSeq005.seqMachine (setMarkerMachine true) (forwardMachine j)
def initSeedMachine (j : Nat) : Machine (initSeedCap j) :=
  PSTRTMSeq005.seqMachine (markerForwardMachine j) farSeedMachine
def initBackMachine (j : Nat) : Machine (initBackCap j) :=
  PSTRTMSeq005.seqMachine (initSeedMachine j) (backwardMachine j)
def bankInitializerMachine (j : Nat) : Machine (bankInitCap j) :=
  PSTRTMSeq005.seqMachine (initBackMachine j) (setMarkerMachine false)

theorem bankInitCap_eq (j : Nat) : bankInitCap j=22*j+12 := by
  unfold bankInitCap initBackCap initSeedCap markerForwardCap
  rw [forwardCap_eq,backwardCap_eq]
  omega

/-- Only the old global footer is written, then fixed-code j record
navigation. The suffix is opaque and can be an already-grown far gap. -/
theorem marker_forward_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive suffix : List Bool) :
    BoundedRun (s:=markerForwardCap j) (markerForwardMachine j)
      (Tape.mk₂ archive (false::bankTail records suffix))
      (PSTRTMSeq005.rightLabel (a:=1) (forwardPort j)) (bankEnd archive records suffix)
      (totalGap records+2*totalWidth records+9*j+3) := by
  have hm : BoundedRun (s:=1) (setMarkerMachine true)
      (Tape.mk₂ archive (false::bankTail records suffix)) 1 (bankStart archive records suffix) 2 :=
    ⟨setMarkerTrace false true archive (bankTail records suffix),
     setMarker_runsFrom false true archive (bankTail records suffix),by rfl⟩
  exact (hm.seq (forward_bounded j records hj archive suffix)).mono (by omega)

/-- Execute ONCE before the outer loop, while the latest record end has
blank tail. No existing n-gap may be overwritten by repeating this seed. -/
theorem bank_initializer_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive : List Bool) :
    BoundedRun (s:=bankInitCap j) (bankInitializerMachine j)
      (Tape.mk₂ archive (false::bankTail records [])) (Fin.last (bankInitCap j))
      (bankTape archive records 0) (2*totalGap records+4*totalWidth records+21*j+13) := by
  have hf := marker_forward_bounded j records hj archive []
  have hs : BoundedRun (s:=initSeedCap j) (initSeedMachine j)
      (Tape.mk₂ archive (false::bankTail records []))
      (PSTRTMSeq005.rightLabel (a:=markerForwardCap j) (6 : Fin 7))
      (bankEnd archive records [true]) (totalGap records+2*totalWidth records+9*j+3+7) :=
    hf.seq (far_seed_bounded (bankLeft archive records))
  have hb : BoundedRun (s:=initBackCap j) (initBackMachine j)
      (Tape.mk₂ archive (false::bankTail records []))
      (PSTRTMSeq005.rightLabel (a:=initSeedCap j) (backwardPort j))
      (bankStart archive records [true])
      ((totalGap records+2*totalWidth records+9*j+3+7)+
        (totalGap records+2*totalWidth records+12*j+1)) :=
    hs.seq (backward_bounded j records hj archive [true])
  have hc : BoundedRun (s:=1) (setMarkerMachine false)
      (bankStart archive records [true]) 1 (bankTape archive records 0) 2 :=
    ⟨setMarkerTrace true false archive (bankTail records [true]),
     setMarker_runsFrom true false archive (bankTail records [true]),by rfl⟩
  exact (hb.seq hc).mono (by omega)

theorem bank_initializer_contract (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive : List Bool) (chargedLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (bankInitializerMachine j)
      ⟨0,Tape.mk₂ archive (false::bankTail records [])⟩ trace
      ⟨Fin.last (bankInitCap j),bankTape archive records 0⟩ ∧
      trace.length≤2*totalGap records+4*totalWidth records+21*j+13 ∧
      ∀ prefixLength, visitedSpace (bankInitializerMachine j) chargedLength (trace.take prefixLength)≤
        chargedLength+4*totalGap records+8*totalWidth records+42*j+27 := by
  obtain ⟨trace,hr,hl⟩ := bank_initializer_bounded j records hj archive
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength
  have hs := PSTRTMTrace002.visitedSpace_le (bankInitializerMachine j) chargedLength (trace.take prefixLength)
  have hp : (trace.take prefixLength).length≤trace.length := by simp only [List.length_take];omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
