module

public import RootB234_PrepExponent_QLoopPotential027

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.QLoop
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource

def loopScale (background : Stack → List Bool) (tail : List Bool) (value : Rat) (count : Nat) : Nat :=
  RatInput.occupied background+tail.length+RatInput.Encoder.fieldSize value+4*count+1

theorem roundsCost_budget (background : Stack → List Bool) (tail : List Bool) (count : Nat)
    (value : Rat) (bound : Nat) (budget : loopScale background tail value count ≤ bound) :
    roundsCost background tail count value ≤ roundCoefficient*(count+1)*bound^4 := by
  induction count generalizing value with
  | zero =>
    have coefficient : 2 ≤ roundCoefficient := by unfold roundCoefficient;omega
    have positive : 1 ≤ bound := by unfold loopScale at budget;omega
    have power : 1 ≤ bound^4 := one_le_pow₀ positive
    change 2 ≤ roundCoefficient*(0+1)*bound^4
    nlinarith only [coefficient,power]
  | succ count ih =>
    have frontScale : roundScale background (List.replicate count true) tail value ≤ bound := by
      unfold roundScale
      rw [List.length_replicate]
      unfold loopScale at budget
      omega
    have front := (roundCost_polynomial background (List.replicate count true) tail value).trans
      (Nat.mul_le_mul_left roundCoefficient (Nat.pow_le_pow_left frontScale 4))
    have doubled := double_field value
    have next : loopScale background tail (2*value) count ≤ bound := by
      unfold loopScale at budget ⊢
      omega
    have back := ih (2*value) next
    change roundCost background (List.replicate count true) tail value+
      roundsCost background tail count (2*value) ≤ roundCoefficient*(count+1+1)*bound^4
    nlinarith only [front,back]

def fullScale (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat) : Nat :=
  RatInput.occupied background+tail.length+RatInput.Encoder.fieldSize budget+number+1

def fullCoefficient : Nat := 65536*roundCoefficient+17179869184+20

theorem fullScale_positive (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat) :
    1 ≤ fullScale background tail budget number := by unfold fullScale;omega

theorem countScale_full (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat)
    (input : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    NCount.scale (bank background (RatInput.Encoder.packet (12 : Rat) (RatInput.Encoder.packet budget tail)) [] [] []) number ≤
      1024*fullScale background tail budget number := by
  let cache := RatInput.Encoder.packet (12 : Rat) (RatInput.Encoder.packet budget tail)
  have each : ∀ slot,(bank background cache [] [] [] slot).length ≤ RatInput.occupied background+cache.length := by
    intro slot
    simpa only [List.length_nil,Nat.add_zero] using bank_length background cache [] [] [] slot
  have mass := RatInput.Encoder.occupied_bound (bank background cache [] [] []) _ each
  have cacheLength : cache.length=22+2*RatInput.Encoder.fieldSize budget+tail.length := by
    dsimp only [cache]
    rw [RatInput.Encoder.packet_length,RatInput.Encoder.packet_length,twelve_field]
    omega
  change RatInput.occupied
    (NCount.bank (bank background cache [] [] []) (B23_4_RatWordPrep.NatField.packet number []) [] [] [] [])+number+1 ≤ _
  rw [count_bank background cache [] number input]
  unfold fullScale
  omega

theorem fullCost_polynomial (background : Stack → List Bool) (tail : List Bool) (budget : Rat) (number : Nat)
    (input : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    fullCost background tail budget number ≤ fullCoefficient*(fullScale background tail budget number)^5 := by
  let S := fullScale background tail budget number
  have positive : 1 ≤ S := fullScale_positive background tail budget number
  have one : 1 ≤ S^5 := one_le_pow₀ positive
  have linear : S ≤ S^5 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (show 1 ≤ 5 by decide)
  have square : S^2 ≤ S^5 := Nat.pow_le_pow_right positive (by decide : 2 ≤ 5)
  have numberBound : number+1 ≤ S := by unfold S fullScale;omega
  have fieldBound : RatInput.Encoder.fieldSize budget ≤ S := by unfold S fullScale;omega
  have countScale := countScale_full background tail budget number input
  have countBound : countCost background
      (RatInput.Encoder.packet (12 : Rat) (RatInput.Encoder.packet budget tail)) number ≤ 17179869184*S^2 := by
    unfold countCost
    exact (Nat.mul_le_mul_left 16384 (Nat.pow_le_pow_left countScale 2)).trans_eq (by dsimp only [S];ring)
  have bodyScale : loopScale background (RatInput.Encoder.packet budget tail) 12 number ≤ 16*S := by
    unfold loopScale
    rw [RatInput.Encoder.packet_length,twelve_field]
    unfold S fullScale
    omega
  have body := roundsCost_budget background (RatInput.Encoder.packet budget tail) number 12 (16*S) bodyScale
  have bodyBound : roundsCost background (RatInput.Encoder.packet budget tail) number 12 ≤
      (65536*roundCoefficient)*S^5 := by
    exact body.trans ((Nat.mul_le_mul_right ((16*S)^4)
      (Nat.mul_le_mul_left roundCoefficient numberBound)).trans_eq (by ring))
  change _ ≤ fullCoefficient*S^5
  unfold fullCost fullCoefficient
  nlinarith only [countBound,bodyBound,square,fieldBound,linear,one]

theorem full_actual_uniform {C : Type*} (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (budget : Rat) (number : Nat)
    (input : background 8=B23_4_RatWordPrep.NatField.packet number []) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state default memory (bank background tail [] (RatInput.Encoder.packet budget []) []))
      (state .done afterMemory
        (bank background (RatInput.Encoder.packet ((12 : Rat)*2^number) (RatInput.Encoder.packet budget tail)) [] [] []))),
      rootContext afterMemory=rootContext memory ∧ afterMemory.2=(false,false) ∧
      part.trace.length ≤ fullCoefficient*(fullScale background tail budget number)^5 := by
  obtain ⟨afterMemory,part,context,flags,count⟩ := full_actual caller background memory tail budget number input
  exact ⟨afterMemory,part,context,flags,count.trans (fullCost_polynomial background tail budget number input)⟩

end RootB234.PrepExponent.QLoop
