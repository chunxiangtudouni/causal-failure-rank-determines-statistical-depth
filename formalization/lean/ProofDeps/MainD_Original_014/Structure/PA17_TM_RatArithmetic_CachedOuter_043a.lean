module
public import Structure.PA17_TM_RatArithmetic_CachedPass_036j
public import Structure.PA17_TM_RatArithmetic_Outer_025c

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedOuter043

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedPass036

def sourceWord (nxTail dxTail nyTail dyTail suffix : List Bool) : List Bool :=
  bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) suffix

def sourceWidth (nxTail dxTail nyTail dyTail : List Bool) : Nat :=
  bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)

def sourceFooter (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks (false::dyTail).reverse++
    false::dyContext sx counter (false::nxTail) (false::dxTail) (false::nyTail))

/-- Read-only source navigation from the real input header to its global
FALSE footer. Every field flag and the two moved-SY cells are traversed. -/
def seekFooterMachine : Machine 18 := PSTRTMSeq005.seqMachine forwardDyMachine scanMachine

theorem seek_footer_bounded (sx : Bool) (counter nxTail dxTail nyTail dyTail suffix : List Bool) :
    BoundedRun (s:=18) seekFooterMachine
      (Tape.mk₂ counter (prefixRight sx (sourceWord nxTail dxTail nyTail dyTail suffix))) 18
      (Tape.mk₂ (sourceFooter sx counter nxTail dxTail nyTail dyTail) (false::suffix))
      (2*sourceWidth nxTail dxTail nyTail dyTail+19) := by
  let nx := false::nxTail
  let dx := false::dxTail
  let ny := false::nyTail
  let dy := false::dyTail
  let tail := true::(PSTRTMIncrement009.blocks dyTail++false::false::suffix)
  have hf : BoundedRun (s:=16) forwardDyMachine
      (Tape.mk₂ counter (prefixRight sx (sourceWord nxTail dxTail nyTail dyTail suffix))) 16
      (Tape.mk₂ (false::dyContext sx counter nx dx ny) (nxStream dy (false::suffix)))
      (2*(nx.length+dx.length+ny.length)+17) :=
    ⟨forwardDyTrace sx counter nx dxTail ny tail,
     forwardDy_runsFrom sx counter nx dxTail ny tail,by rw [forwardDyTrace_length]⟩
  have hs : BoundedRun (s:=1) scanMachine
      (Tape.mk₂ (false::dyContext sx counter nx dx ny) (nxStream dy (false::suffix))) 1
      (Tape.mk₂ (sourceFooter sx counter nxTail dxTail nyTail dyTail) (false::suffix)) (2*dy.length+2) :=
    ⟨scanTrace (false::dyContext sx counter nx dx ny) dy false suffix,
     scan_runsFrom (false::dyContext sx counter nx dx ny) dy false suffix,by rw [scanTrace_length]⟩
  exact (hf.seq hs).mono (by dsimp only [nx,dx,ny,dy,sourceWidth,bankWidth];omega)

def seedAtFooterCap (j : Nat) : Nat := 18+bankInitCap j+1
def seedHomeCap (j : Nat) : Nat := seedAtFooterCap j+34+1
attribute [local implicit_reducible] seedAtFooterCap seedHomeCap

def seedAtFooterMachine (j : Nat) : Machine (seedAtFooterCap j) :=
  PSTRTMSeq005.seqMachine seekFooterMachine (bankInitializerMachine j)
def seedHomeMachine (j : Nat) : Machine (seedHomeCap j) :=
  PSTRTMSeq005.seqMachine (seedAtFooterMachine j) finishBackMachine

theorem seedHomeCap_eq (j : Nat) : seedHomeCap j=22*j+66 := by
  unfold seedHomeCap seedAtFooterCap
  rw [bankInitCap_eq]
  omega

/-- One-time real far seed followed by the physical source rewind. The
latest cached end has blank right tail initially; an existing gap must
never be overwritten by repeating this initialization. -/
theorem seed_home_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) :
    BoundedRun (s:=seedHomeCap j) (seedHomeMachine j)
      (Tape.mk₂ counter (prefixRight sx
        (sourceWord nxTail dxTail nyTail dyTail (bankTail records []))))
      (Fin.last (seedHomeCap j))
      (Tape.mk₂ counter (prefixRight sx
        (sourceWord nxTail dxTail nyTail dyTail (cachedTail records 0))))
      (4*sourceWidth nxTail dxTail nyTail dyTail+2*totalGap records+4*totalWidth records+21*j+63) := by
  let archive := sourceFooter sx counter nxTail dxTail nyTail dyTail
  have hf := seek_footer_bounded sx counter nxTail dxTail nyTail dyTail (bankTail records [])
  have hs := bank_initializer_bounded j records hj archive
  have hfirst : BoundedRun (s:=seedAtFooterCap j) (seedAtFooterMachine j)
      (Tape.mk₂ counter (prefixRight sx (sourceWord nxTail dxTail nyTail dyTail (bankTail records []))))
      (PSTRTMSeq005.rightLabel (a:=18) (Fin.last (bankInitCap j)))
      (bankTape archive records 0)
      ((2*sourceWidth nxTail dxTail nyTail dyTail+19)+
        (2*totalGap records+4*totalWidth records+21*j+13)) := hf.seq hs
  have hb := finishBack_bounded sx counter (false::nxTail) (false::dxTail) (false::nyTail)
    (false::dyTail) (cachedTail records 0)
  exact (hfirst.seq hb).mono (by unfold sourceWidth;omega)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedOuter043
