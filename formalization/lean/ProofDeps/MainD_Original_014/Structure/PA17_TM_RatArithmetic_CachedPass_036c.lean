module
public import Structure.PA17_TM_RatArithmetic_CachedPass_036b

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013.expandCap
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankWalk033.forwardCap
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankWalk033.backwardCap
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036

open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticAllocate013 (setMarkerMachine setMarkerTrace setMarker_runsFrom expandMachine expandCap expandLast)

attribute [local implicit_reducible] markerForwardCap

theorem set_marker_bounded (newBit oldBit : Bool) (archive suffix : List Bool) :
    BoundedRun (s:=1) (setMarkerMachine newBit) (Tape.mk₂ archive (oldBit::suffix)) 1
      (Tape.mk₂ archive (newBit::suffix)) 2 :=
  ⟨setMarkerTrace oldBit newBit archive suffix,setMarker_runsFrom oldBit newBit archive suffix,by rfl⟩

def roundClearCap (j : Nat) : Nat := markerForwardCap j+1+1
def roundExpandCap (j k : Nat) : Nat := roundClearCap j+expandCap k+1
def roundRestoreCap (j k : Nat) : Nat := roundExpandCap j k+1+1
def roundReturnCap (j k : Nat) : Nat := roundRestoreCap j k+backwardCap j+1
def bankRoundCap (j k : Nat) : Nat := roundReturnCap j k+1+1
attribute [local implicit_reducible] roundClearCap roundExpandCap roundRestoreCap roundReturnCap bankRoundCap

def roundClearMachine (j : Nat) : Machine (roundClearCap j) :=
  PSTRTMSeq005.seqMachine (markerForwardMachine j) (setMarkerMachine false)
def roundExpandMachine (j k : Nat) : Machine (roundExpandCap j k) :=
  PSTRTMSeq005.seqMachine (roundClearMachine j) (expandMachine k)
def roundRestoreMachine (j k : Nat) : Machine (roundRestoreCap j k) :=
  PSTRTMSeq005.seqMachine (roundExpandMachine j k) (setMarkerMachine true)
def roundReturnMachine (j k : Nat) : Machine (roundReturnCap j k) :=
  PSTRTMSeq005.seqMachine (roundRestoreMachine j k) (backwardMachine j)
def bankRoundMachine (j k : Nat) : Machine (bankRoundCap j k) :=
  PSTRTMSeq005.seqMachine (roundReturnMachine j k) (setMarkerMachine false)

theorem bankRoundCap_eq (j k : Nat) : bankRoundCap j k=22*j+15*k+19 := by
  unfold bankRoundCap roundReturnCap roundRestoreCap roundExpandCap roundClearCap markerForwardCap
  rw [forwardCap_eq,backwardCap_eq]
  unfold expandCap totalStates
  omega

def bankRoundFee (j k : Nat) (records : List RecordSpec) (n : Nat) : Nat :=
  2*totalGap records+4*totalWidth records+21*j+2*n+4*k+19

/-- The global footer and latest record end are written and restored
physically. The temporary source FLAG can therefore be the last Dy FLAG;
no FALSE-footer scanner ever assumes that source flag remains TRUE. -/
theorem bank_round_bounded (j k : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive : List Bool) (n : Nat) :
    BoundedRun (s:=bankRoundCap j k) (bankRoundMachine j k) (bankTape archive records n)
      (Fin.last (bankRoundCap j k)) (bankTape archive records (n+k)) (bankRoundFee j k records n) := by
  have hf := marker_forward_bounded j records hj archive (gapWord n)
  have hc : BoundedRun (s:=roundClearCap j) (roundClearMachine j)
      (bankTape archive records n)
      (PSTRTMSeq005.rightLabel (a:=markerForwardCap j) (1 : Fin 2))
      (Tape.mk₂ (bankLeft archive records) (false::gapWord n))
      (totalGap records+2*totalWidth records+9*j+3+2) :=
    hf.seq (set_marker_bounded false true (bankLeft archive records) (gapWord n))
  have he : BoundedRun (s:=roundExpandCap j k) (roundExpandMachine j k)
      (bankTape archive records n)
      (PSTRTMSeq005.rightLabel (a:=roundClearCap j) (expandLast k n (bankLeft archive records)).q)
      (Tape.mk₂ (bankLeft archive records) (false::gapWord (n+k)))
      ((totalGap records+2*totalWidth records+9*j+3+2)+(2*n+4*k+9)) :=
    hc.seq (PA17TMRatArithmeticAllocatePass023.expand_bounded k n (bankLeft archive records))
  have ht : BoundedRun (s:=roundRestoreCap j k) (roundRestoreMachine j k)
      (bankTape archive records n)
      (PSTRTMSeq005.rightLabel (a:=roundExpandCap j k) (1 : Fin 2))
      (bankEnd archive records (gapWord (n+k)))
      (((totalGap records+2*totalWidth records+9*j+3+2)+(2*n+4*k+9))+2) :=
    he.seq (set_marker_bounded true false (bankLeft archive records) (gapWord (n+k)))
  have hb : BoundedRun (s:=roundReturnCap j k) (roundReturnMachine j k)
      (bankTape archive records n)
      (PSTRTMSeq005.rightLabel (a:=roundRestoreCap j k) (backwardPort j))
      (bankStart archive records (gapWord (n+k)))
      ((((totalGap records+2*totalWidth records+9*j+3+2)+(2*n+4*k+9))+2)+
        (totalGap records+2*totalWidth records+12*j+1)) :=
    ht.seq (backward_bounded j records hj archive (gapWord (n+k)))
  exact (hb.seq (set_marker_bounded false true archive (bankTail records (gapWord (n+k))))).mono
    (by unfold bankRoundFee;omega)

theorem bank_round_contract (j k : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive : List Bool) (n chargedLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (bankRoundMachine j k) ⟨0,bankTape archive records n⟩ trace
      ⟨Fin.last (bankRoundCap j k),bankTape archive records (n+k)⟩ ∧
      trace.length≤bankRoundFee j k records n ∧
      ∀ prefixLength, visitedSpace (bankRoundMachine j k) chargedLength (trace.take prefixLength)≤
        chargedLength+2*bankRoundFee j k records n+1 := by
  obtain ⟨trace,hr,hl⟩ := bank_round_bounded j k records hj archive n
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength
  have hs := PSTRTMTrace002.visitedSpace_le (bankRoundMachine j k) chargedLength (trace.take prefixLength)
  have hp : (trace.take prefixLength).length≤trace.length := by simp only [List.length_take];omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
