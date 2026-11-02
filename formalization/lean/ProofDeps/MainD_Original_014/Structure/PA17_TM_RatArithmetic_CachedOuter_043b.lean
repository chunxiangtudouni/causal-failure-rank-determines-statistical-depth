module
public import Structure.PA17_TM_RatArithmetic_CachedOuter_043a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedOuter043
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedPass036

/-- Pure physical refill: seven RIGHT moves, then frozen middle645.
No raw parser, decoder, memory projection or bit-tuple argument occurs. -/
def refillMachine : Machine 653 := PSTRTMSeq005.seqMachine forwardNxMachine middleMachine

def refillFee (width : Nat) : Nat := width*(6*width+68)+56

theorem refill_bounded (sx : Bool) (nxTail dxTail nyTail dyTail suffix : List Bool) :
    BoundedRun (s:=653) refillMachine
      (Tape.mk₂ [false] (prefixRight sx (sourceWord nxTail dxTail nyTail dyTail suffix))) 653
      (Tape.mk₂ (false::ROOTTMGCDCounter011.ones (sourceWidth nxTail dxTail nyTail dyTail))
        (prefixRight sx (sourceWord nxTail dxTail nyTail dyTail suffix)))
      (refillFee (sourceWidth nxTail dxTail nyTail dyTail)) := by
  let word := sourceWord nxTail dxTail nyTail dyTail suffix
  have hf : BoundedRun (s:=7) forwardNxMachine
      (Tape.mk₂ [false] (prefixRight sx word)) 7 (Tape.mk₂ (prefixLeft sx [false]) word) 8 :=
    ⟨forwardNxTrace sx [false] word,forwardNx_runsFrom sx [false] word,by rfl⟩
  have hm : BoundedRun (s:=645) middleMachine (Tape.mk₂ (prefixLeft sx [false]) word) 645
      (Tape.mk₂ (false::ROOTTMGCDCounter011.ones (sourceWidth nxTail dxTail nyTail dyTail))
        (prefixRight sx word))
      (sourceWidth nxTail dxTail nyTail dyTail*(6*sourceWidth nxTail dxTail nyTail dyTail+68)+48) := by
    have hl : false::nxContext sx (false::ROOTTMGCDCounter011.ones 0)=prefixLeft sx [false] := rfl
    have hm := middle_bounded sx 0 nxTail dxTail nyTail dyTail suffix
    rw [hl] at hm
    simpa only [word,sourceWord,sourceWidth,Nat.mul_zero,Nat.zero_add] using hm
  exact (hf.seq hm).mono (by unfold refillFee;omega)

def prepareCap (j : Nat) : Nat := seedHomeCap j+653+1
attribute [local implicit_reducible] prepareCap

def prepareMachine (j : Nat) : Machine (prepareCap j) :=
  PSTRTMSeq005.seqMachine (seedHomeMachine j) refillMachine

theorem prepareCap_eq (j : Nat) : prepareCap j=22*j+720 := by
  unfold prepareCap
  rw [seedHomeCap_eq]

def prepareFee (j : Nat) (records : List RecordSpec) (width : Nat) : Nat :=
  4*width+2*totalGap records+4*totalWidth records+21*j+63+refillFee width

/-- One seed, one real W-refill. The old source and every cache record
are unchanged; the actual left unary counter now contains exactly W. -/
theorem prepare_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool) :
    BoundedRun (s:=prepareCap j) (prepareMachine j)
      (Tape.mk₂ [false] (prefixRight sx
        (sourceWord nxTail dxTail nyTail dyTail (bankTail records []))))
      (Fin.last (prepareCap j))
      (Tape.mk₂ (false::ROOTTMGCDCounter011.ones (sourceWidth nxTail dxTail nyTail dyTail))
        (prefixRight sx (sourceWord nxTail dxTail nyTail dyTail (cachedTail records 0))))
      (prepareFee j records (sourceWidth nxTail dxTail nyTail dyTail)) := by
  have hs := seed_home_bounded j records hj sx [false] nxTail dxTail nyTail dyTail
  have hr := refill_bounded sx nxTail dxTail nyTail dyTail (cachedTail records 0)
  exact (hs.seq hr).mono (by unfold prepareFee;omega)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedOuter043
