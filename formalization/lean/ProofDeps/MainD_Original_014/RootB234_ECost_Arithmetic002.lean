module

public import RootB234_ECost_Widths001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.ECost

open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM RootL01.SymbolicSource
open RootB234.PrepExponent

def binaryScale (background : Bank) (cache counter : List Bool) (x y : Rat) (tail : List Bool) : Nat :=
  RatInput.occupied background+cache.length+counter.length+tail.length+field x+field y+1

theorem binaryScale_pos (background : Bank) (cache counter : List Bool) (x y : Rat) (tail : List Bool) :
    1 ≤ binaryScale background cache counter x y tail := by unfold binaryScale; omega

theorem pair_space (background : Bank) (cache counter : List Bool) (x y : Rat) (tail : List Bool) :
    RatPair.space (QLoop.rawBackground background cache counter) x y tail cache ≤
      8192*binaryScale background cache counter x y tail := by
  let contents := QLoop.rawBackground background cache counter
  have each : ∀ slot, (contents slot).length ≤ RatInput.occupied background+cache.length+counter.length := by
    intro slot
    dsimp only [contents,QLoop.rawBackground,StackIso.slots]
    simpa only [List.length_nil,Nat.add_zero,Equiv.symm_symm] using
      QLoop.bank_length background cache counter [] [] (Arithmetic.binaryRoles slot)
  have mass := RatInput.Encoder.occupied_bound contents _ each
  have outside := (QLoop.pair_outside contents).trans mass
  change RatPair.Link.outside contents+tail.length+cache.length+258*RatPair.fieldSize x y+2572 ≤ _
  rw [RatBinary.fieldSize_eq]
  unfold binaryScale
  dsimp only [field]
  omega

def binarySpaceCoefficient (coefficient : Nat) : Nat := 1000000+coefficient*1000000^4
def binaryTimeCoefficient (coefficient : Nat) : Nat := 7*binarySpaceCoefficient coefficient+200

theorem binary_space (coefficient : Nat) (background : Bank) (cache counter : List Bool)
    (x y : Rat) (tail : List Bool) :
    RatBinary.space coefficient (QLoop.rawBackground background cache counter) x y tail cache ≤
      binarySpaceCoefficient coefficient*(binaryScale background cache counter x y tail)^4 := by
  let S := binaryScale background cache counter x y tail
  let P := RatPair.space (QLoop.rawBackground background cache counter) x y tail cache
  have positive : 1 ≤ S := binaryScale_pos background cache counter x y tail
  have power : S ≤ S^4 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (show 1 ≤ 4 by decide)
  have bound : P ≤ 8192*S := pair_space background cache counter x y tail
  have base : 16*P+1 ≤ 1000000*S := by omega
  have nonlinear : RatBinary.rawBound coefficient (QLoop.rawBackground background cache counter) x y tail cache ≤
      coefficient*1000000^4*S^4 := by
    change coefficient*(16*P+1)^4 ≤ _
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 4)).trans_eq (by ring)
  have linear : 16*P+8 ≤ 1000000*S^4 := by omega
  change 16*P+RatBinary.rawBound coefficient (QLoop.rawBackground background cache counter) x y tail cache+8 ≤ _
  unfold binarySpaceCoefficient
  nlinarith only [linear,nonlinear]

theorem binary_time (coefficient : Nat) (background : Bank) (cache counter : List Bool)
    (x y : Rat) (tail : List Bool) :
    RatBinary.time coefficient (QLoop.rawBackground background cache counter) x y tail cache ≤
      binaryTimeCoefficient coefficient*(binaryScale background cache counter x y tail)^4 := by
  let S := binaryScale background cache counter x y tail
  have positive : 1 ≤ S := binaryScale_pos background cache counter x y tail
  have power : S ≤ S^4 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (show 1 ≤ 4 by decide)
  have one : 1 ≤ S^4 := one_le_pow₀ positive
  have fields : field x+field y ≤ S := by unfold S binaryScale; omega
  have space := binary_space coefficient background cache counter x y tail
  change _ ≤ binarySpaceCoefficient coefficient*S^4 at space
  change _ ≤ binaryTimeCoefficient coefficient*S^4
  unfold RatBinary.time
  rw [RatBinary.fieldSize_eq]
  unfold binaryTimeCoefficient
  dsimp only [field] at fields ⊢
  nlinarith only [space,fields,power,one]

theorem binary_time_budget (coefficient : Nat) (background : Bank) (cache counter : List Bool)
    (x y : Rat) (tail : List Bool) (B : Nat)
    (bounded : binaryScale background cache counter x y tail ≤ 1024*B) :
    RatBinary.time coefficient (QLoop.rawBackground background cache counter) x y tail cache ≤
      (binaryTimeCoefficient coefficient*1024^4)*B^4 := by
  exact (binary_time coefficient background cache counter x y tail).trans
    ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bounded 4)).trans_eq (by ring))

theorem global_bank_mass (background : Bank) (cache : List Bool) :
    RatInput.occupied (Global.bank background cache [] [] [] [] []) ≤
      16*(RatInput.occupied background+cache.length) := by
  apply RatInput.Encoder.occupied_bound
  intro slot
  have old := RatInput.Encoder.point_mass background slot
  unfold Global.bank
  split_ifs <;> (try simp only [List.length_nil]) <;> omega

theorem natural_scale (background : Bank) (number : Nat) (tail : List Bool) :
    NatToRat.scale background number tail ≤
      1024*(RatInput.occupied background+tail.length+number+1) := by
  have width := raw_length number
  have packet := natural_packet_length number []
  simp only [List.length_nil,Nat.add_zero] at packet
  have each : ∀ slot,
      (NatToRat.bank background (B23_4_RatWordPrep.NatField.packet number []) [] [] tail slot).length ≤
        RatInput.occupied background+2*number+4+tail.length := by
    intro slot
    have old := RatInput.Encoder.point_mass background slot
    unfold NatToRat.bank
    split_ifs <;> (try simp only [List.length_nil]) <;> omega
  have mass := RatInput.Encoder.occupied_bound _ _ each
  change RatInput.occupied _+1 ≤ _
  omega

end RootB234.ECost
