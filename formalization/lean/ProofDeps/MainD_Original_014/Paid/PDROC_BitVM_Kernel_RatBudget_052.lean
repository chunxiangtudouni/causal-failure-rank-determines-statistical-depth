module

public import Paid.PDROC_BitVM_Kernel_RatInstruction_048

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawInstruction

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

def resourceCoefficient {states : ℕ} (machine : Machine states) (left right : Register) (c d : ℕ) : ℕ :=
  (1+320*pushCap machine left right)*(13+c*7^d)+400

theorem resourceCoefficient_positive {states : ℕ} (machine : Machine states) (left right : Register) (c d : ℕ) :
    0<resourceCoefficient machine left right c d := by
  dsimp only [resourceCoefficient]
  omega

/-- The original two-Rat native input length is bounded by the ACTUAL
represented entry Cells. Unrelated carried data is included in dataSize,
so the bound never assumes an input-only allowance for arbitrary scratch. -/
theorem represented_lengths (logical : PaperProofs.Paid.Computation.State) (left right : Register) (x y : Rat)
    (contents : Stack → List Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftRat : logical.register left=.rational x) (rightRat : logical.register right=.rational y) :
    (encodeCellBits (logical.register left)).length ≤ NatInstruction.dataSize contents ∧
    (encodeCellBits (logical.register right)).length ≤ NatInstruction.dataSize contents ∧
    (encode [.rational x,.rational y]).length+1 ≤ 7*(NatInstruction.dataSize contents+1) := by
  have leftBound : (encodeCellBits (logical.register left)).length ≤ NatInstruction.dataSize contents := by
    rw [← represented left]
    exact NatInstruction.dataSize_each contents (registerSlot left)
  have rightBound : (encodeCellBits (logical.register right)).length ≤ NatInstruction.dataSize contents := by
    rw [← represented right]
    exact NatInstruction.dataSize_each contents (registerSlot right)
  refine ⟨leftBound,rightBound,?_⟩
  have rawLength : (encode [.rational x,.rational y]).length=
      (encodeCellBits (logical.register left)).length+(encodeCellBits (logical.register right)).length+6 := by
    rw [leftRat,rightRat]
    have headerLength : (encodeNat 2).length=5 := rfl
    simp only [encode,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]
    change (encodeNat 2).length+
      ((encodeCellBits (.rational x)).length+(encodeCellBits (.rational y)).length)+1=_
    rw [headerLength]
    omega
  rw [rawLength]
  omega

theorem computeBudget_polynomial (logical : PaperProofs.Paid.Computation.State) (left right : Register)
    (x y : Rat) (c d : ℕ) (positiveD : 0<d) (contents : Stack → List Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftRat : logical.register left=.rational x) (rightRat : logical.register right=.rational y) :
    computeBudget logical left right x y c d ≤
      (13+c*7^d)*(NatInstruction.dataSize contents+1)^d := by
  obtain ⟨leftBound,rightBound,inputBound⟩ := represented_lengths logical left right x y contents represented leftRat rightRat
  let D := NatInstruction.dataSize contents
  let power := (D+1)^d
  have grows : D+1 ≤ power := by
    simpa only [pow_one,power] using Nat.pow_le_pow_right (by omega : 1 ≤ D+1) (by omega : 1 ≤ d)
  have small : 2*(encodeCellBits (logical.register left)).length+
      2*(encodeCellBits (logical.register right)).length+9 ≤ 13*power := by
    change (encodeCellBits (logical.register left)).length ≤ D at leftBound
    change (encodeCellBits (logical.register right)).length ≤ D at rightBound
    omega
  have native : c*((encode [.rational x,.rational y]).length+1)^d ≤ c*7^d*power := by
    calc
      _ ≤ c*(7*(D+1))^d := Nat.mul_le_mul_left c (Nat.pow_le_pow_left inputBound d)
      _ = c*7^d*power := by rw [mul_pow];dsimp only [power];ring
  calc
    _ = (2*(encodeCellBits (logical.register left)).length+
        2*(encodeCellBits (logical.register right)).length+9)+c*((encode [.rational x,.rational y]).length+1)^d := by
      dsimp only [computeBudget]
      ring
    _ ≤ 13*power+c*7^d*power := Nat.add_le_add small native
    _ = (13+c*7^d)*(NatInstruction.dataSize contents+1)^d := by dsimp only [power,D];ring

/-- A polynomial in actual complete entry data bounds the WHOLE original
rational instruction, including native padding and all destination/work
cleanup. Its coefficient/degree depend only on fixed code/native constants. -/
theorem budget_polynomial {states : ℕ} (machine : Machine states)
    (logical : PaperProofs.Paid.Computation.State) (left right : Register) (x y : Rat)
    (c d : ℕ) (positiveD : 0<d) (contents : Stack → List Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftRat : logical.register left=.rational x) (rightRat : logical.register right=.rational y) :
    budget machine logical left right x y c d contents ≤
      resourceCoefficient machine left right c d*(NatInstruction.dataSize contents+1)^d := by
  let D := NatInstruction.dataSize contents
  let power := (D+1)^d
  have grows : D+1 ≤ power := by
    simpa only [pow_one,power] using Nat.pow_le_pow_right (by omega : 1 ≤ D+1) (by omega : 1 ≤ d)
  have compute := computeBudget_polynomial logical left right x y c d positiveD contents represented leftRat rightRat
  have small : 320*D+69 ≤ 400*power := by omega
  calc
    _ = (1+320*pushCap machine left right)*computeBudget logical left right x y c d+320*D+69 := by
      dsimp only [budget,ceiling,D]
      ring
    _ ≤ (1+320*pushCap machine left right)*((13+c*7^d)*power)+400*power := by
      have large := Nat.mul_le_mul_left (1+320*pushCap machine left right) compute
      change (1+320*pushCap machine left right)*computeBudget logical left right x y c d ≤
        (1+320*pushCap machine left right)*((13+c*7^d)*power) at large
      omega
    _ = resourceCoefficient machine left right c d*(NatInstruction.dataSize contents+1)^d := by
      dsimp only [resourceCoefficient,power,D]
      ring

end PDROC.BitVM.Kernel.RawInstruction
