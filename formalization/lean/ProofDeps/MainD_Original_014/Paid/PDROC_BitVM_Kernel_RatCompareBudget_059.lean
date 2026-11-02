module

public import Paid.PDROC_BitVM_Kernel_RatCompareResources_056

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RatCompare

open PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

def resourceCoefficient {states : ℕ} (machine : Machine states) (target left right : Register)
    (c d : ℕ) : ℕ :=
  (1+64*differenceCap machine target left right)*RawInstruction.resourceCoefficient machine left right c d+392

theorem resourceCoefficient_positive {states : ℕ} (machine : Machine states)
    (target left right : Register) (c d : ℕ) :
    0 < resourceCoefficient machine target left right c d := by
  dsimp only [resourceCoefficient]
  omega

/-- The actual four-macro comparison path is polynomial in the whole
entry data. The difference machine, all coefficients and the degree are
fixed before operands, and carried workspace is charged in dataSize. -/
theorem budget_polynomial {states : ℕ} (machine : Machine states)
    (logical : PaperProofs.Paid.Computation.State) (target left right : Register)
    (x y : Rat) (c d : ℕ) (positiveD : 0 < d) (contents : Stack → List Bool)
    (represented : ∀ reg, contents (RegisterGlobal.registerSlot reg) = encodeCellBits (logical.register reg))
    (leftRat : logical.register left = .rational x) (rightRat : logical.register right = .rational y) :
    budget machine logical target left right x y c d contents ≤
      resourceCoefficient machine target left right c d*(NatInstruction.dataSize contents+1)^d := by
  let D := NatInstruction.dataSize contents
  let power := (D+1)^d
  have grows : D+1 ≤ power := by
    simpa only [pow_one,power] using
      Nat.pow_le_pow_right (by omega : 1 ≤ D+1) (by omega : 1 ≤ d)
  have raw := RawInstruction.budget_polynomial machine logical left right x y c d positiveD contents
    represented leftRat rightRat
  have small : 64*D+328 ≤ 392*power := by omega
  calc
    _ = (1+64*differenceCap machine target left right)*
        RawInstruction.budget machine logical left right x y c d contents+64*D+328 := by
      dsimp only [budget,D]
      ring
    _ ≤ (1+64*differenceCap machine target left right)*
        (RawInstruction.resourceCoefficient machine left right c d*power)+392*power := by
      have large := Nat.mul_le_mul_left (1+64*differenceCap machine target left right) raw
      change (1+64*differenceCap machine target left right)*
        RawInstruction.budget machine logical left right x y c d contents ≤
        (1+64*differenceCap machine target left right)*
        (RawInstruction.resourceCoefficient machine left right c d*power) at large
      omega
    _ = resourceCoefficient machine target left right c d*(NatInstruction.dataSize contents+1)^d := by
      dsimp only [resourceCoefficient,power,D]
      ring

end PDROC.BitVM.Kernel.RatCompare
