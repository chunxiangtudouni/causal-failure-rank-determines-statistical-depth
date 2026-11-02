module
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023j

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
open PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014

/-- Literal fixed-cap ABI: initial0 at Nx, real HALT at the max label and
original header, unchanged unary h and original source, gap n+kW. -/
theorem pass_bounded (k : Nat) (sx : Bool) (h n : Nat) (nxTail dxTail nyTail dyTail : List Bool) :
    BoundedRun (passMachine k)
      (Turing.Tape.mk₂ (false::nxContext sx (false::ROOTTMGCDCounter011.ones h))
        (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) (gapTail n)))
      (Fin.last (passCap k))
      (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones h)
        (prefixRight sx (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)
          (gapTail (n+k*bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail))))))
      (passFee k (bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)) n) := by
  have hr := (raw_pass_bounded k sx h n nxTail dxTail nyTail dyTail).pad (Nat.le_of_eq (rawPassCap_eq k))
  have hq : padLabel (Nat.le_of_eq (rawPassCap_eq k)) (Fin.last (rawPassCap k))=Fin.last (passCap k) := by
    apply Fin.ext
    exact rawPassCap_eq k
  rw [hq] at hr
  exact hr

theorem original_pass_bounded (k h n : Nat) (x y : Rat) :
    BoundedRun (passMachine k)
      (Turing.Tape.mk₂ (false::nxContext (sign x) (false::ROOTTMGCDCounter011.ones h))
        (originalBank x y (gapTail n))) (Fin.last (passCap k))
      (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones h)
        (prefixRight (sign x) (originalBank x y (gapTail (n+k*fieldWidth x y)))))
      (passFee k (fieldWidth x y) n) := by
  have hr := pass_bounded k (sign x) h n (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail
  change BoundedRun (passMachine k)
    (Turing.Tape.mk₂ (false::nxContext (sign x) (false::ROOTTMGCDCounter011.ones h))
      (originalBank x y (gapTail n))) (Fin.last (passCap k))
    (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones h)
      (prefixRight (sign x) (originalBank x y (gapTail (n+k*bankWidth
        (clampFirst (numeratorDigits x)) (clampFirst (denominatorDigits x))
        (clampFirst (numeratorDigits y)) (clampFirst (denominatorDigits y)))))))
    (passFee k (bankWidth (clampFirst (numeratorDigits x)) (clampFirst (denominatorDigits x))
      (clampFirst (numeratorDigits y)) (clampFirst (denominatorDigits y))) n) at hr
  rw [originalWidth_eq] at hr
  exact hr

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
