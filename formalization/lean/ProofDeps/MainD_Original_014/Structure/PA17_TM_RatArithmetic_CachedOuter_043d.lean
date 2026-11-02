module
public import Structure.PA17_TM_RatArithmetic_CachedOuter_043c

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedOuter043
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedPass036

def outerCap (j k : Nat) : Nat := prepareCap j+cachedLoopCap j k+1
attribute [local implicit_reducible] prepareCap cachedLoopCap outerCap

def outerMachine (j k : Nat) : Machine (outerCap j k) :=
  PSTRTMSeq005.seqMachine (prepareMachine j) (cachedLoopMachine j k)

def outerPort (j k : Nat) : Fin (outerCap j k+1) :=
  PSTRTMSeq005.rightLabel (a:=prepareCap j) (cachedLoopPort j k)

theorem outerCap_eq (j k : Nat) : outerCap j k=240*k+374*j+2076 := by
  unfold outerCap cachedLoopCap totalStates cachedPassCap
  rw [prepareCap_eq]
  omega

theorem outerPort_value (j k : Nat) : (outerPort j k).val=22*j+728 := by
  simp only [outerPort,PSTRTMSeq005.rightLabel,cachedLoopPort_value,prepareCap_eq]

def outerFee (j k : Nat) (records : List RecordSpec) (width : Nat) : Nat :=
  prepareFee j records width+loopFee j k records width

theorem sourceWidth_ge_four (nxTail dxTail nyTail dyTail : List Bool) :
    4≤sourceWidth nxTail dxTail nyTail dyTail := by
  unfold sourceWidth bankWidth
  simp only [List.length_cons]
  omega

/-- The gap is created by the actual loop below. Positive k is a code
choice, not an extra condition on the original rational input. -/
theorem grownGap_ge_three (k : Nat) (hk : 0<k) (nxTail dxTail nyTail dyTail : List Bool) :
    3≤k*(sourceWidth nxTail dxTail nyTail dyTail)^2 := by
  have hw := sourceWidth_ge_four nxTail dxTail nyTail dyTail
  have hs : 16≤(sourceWidth nxTail dxTail nyTail dyTail)^2 := by nlinarith
  have hm := Nat.mul_le_mul_right ((sourceWidth nxTail dxTail nyTail dyTail)^2) (by omega : 1≤k)
  simp only [Nat.one_mul] at hm
  omega

/-- Full real seed/refill/pop allocation. No record, W, G, V, current
counter or desired gap is an argument of this fixed j/k program. -/
theorem outer_bounded (j k : Nat) (records : List RecordSpec) (hj : records.length=j)
    (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool) :
    BoundedRun (s:=outerCap j k) (outerMachine j k)
      (Tape.mk₂ [false] (prefixRight sx (sourceWord nxTail dxTail nyTail dyTail (bankTail records []))))
      (outerPort j k)
      (Tape.mk₂ [false] (prefixRight sx (sourceWord nxTail dxTail nyTail dyTail
        (cachedTail records (k*(sourceWidth nxTail dxTail nyTail dyTail)^2)))))
      (outerFee j k records (sourceWidth nxTail dxTail nyTail dyTail)) := by
  have hp := prepare_bounded j records hj sx nxTail dxTail nyTail dyTail
  have hl := counted_loop_bounded j k records hj sx nxTail dxTail nyTail dyTail
  exact hp.seq hl

theorem original_outer_bounded (j k : Nat) (records : List RecordSpec) (hj : records.length=j)
    (x y : Rat) :
    BoundedRun (s:=outerCap j k) (outerMachine j k)
      (Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (bankTail records []))))
      (outerPort j k)
      (Tape.mk₂ [false] (prefixRight (sign x)
        (originalBank x y (cachedTail records (k*(fieldWidth x y)^2)))))
      (outerFee j k records (fieldWidth x y)) := by
  have hr := outer_bounded j k records hj (sign x) (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail
  change BoundedRun (s:=outerCap j k) (outerMachine j k)
    (Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (bankTail records [])))) (outerPort j k)
    (Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (cachedTail records (k*(bankWidth
      (clampFirst (numeratorDigits x)) (clampFirst (denominatorDigits x))
      (clampFirst (numeratorDigits y)) (clampFirst (denominatorDigits y)))^2)))))
    (outerFee j k records (bankWidth (clampFirst (numeratorDigits x)) (clampFirst (denominatorDigits x))
      (clampFirst (numeratorDigits y)) (clampFirst (denominatorDigits y)))) at hr
  rw [originalWidth_eq] at hr
  exact hr

/-- The bound retains every actual cache traversal term. A pure original
input polynomial requires the caller's genuine G/V size invariant. -/
theorem original_outer_contract (j k : Nat) (records : List RecordSpec) (hj : records.length=j)
    (x y : Rat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (outerMachine j k)
      ⟨0,Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (bankTail records [])))⟩ trace
      ⟨outerPort j k,Tape.mk₂ [false] (prefixRight (sign x)
        (originalBank x y (cachedTail records (k*(fieldWidth x y)^2))))⟩ ∧
      trace.length≤outerFee j k records (fieldWidth x y) ∧
      ∀ prefixLength, visitedSpace (outerMachine j k) (encode [.rational x,.rational y]).length
        (trace.take prefixLength) ≤
        (encode [.rational x,.rational y]).length+2*outerFee j k records (fieldWidth x y)+1 := by
  obtain ⟨trace,hr,hl⟩ := original_outer_bounded j k records hj x y
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength
  have hs := PSTRTMTrace002.visitedSpace_le (outerMachine j k)
    (encode [.rational x,.rational y]).length (trace.take prefixLength)
  have hp : (trace.take prefixLength).length≤trace.length := by simp only [List.length_take];omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedOuter043
