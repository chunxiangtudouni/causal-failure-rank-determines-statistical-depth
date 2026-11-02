module

public import Structure.RootB23_Threshold_Window_PayloadFour_024

/-! Fixed polynomial cost of the actual four-copy/restore/anchor execution.
The gap is an actually allocated tape region, not a machine argument. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadCost
open Turing PSTRTMSeq005
open PA17TMRatArithmeticWidth018 (BoundedRun)

theorem copy_fee_le (tail : List Bool) (cost room : Nat) (positive : 1 ≤ room)
    (digits : (false :: tail).length ≤ room) (costBound : cost ≤ 12 * room + 123) :
    PayloadSteps.copyFee tail cost ≤ 1024 * room ^ 2 := by
  have square := Nat.mul_le_mul digits digits
  have coefficient : 2 * cost + 41 ≤ 24 * room + 287 := by omega
  have product := Nat.mul_le_mul coefficient digits
  have linear : room ≤ room ^ 2 := by
    simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left room positive
  have one : 1 ≤ room ^ 2 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right positive (by decide : 0 ≤ 2)
  unfold PayloadSteps.copyFee
  nlinarith

theorem fee_le (n gap memory : Nat) (nx dx ny dy : List Bool) :
    PayloadFour.fee n gap memory nx dx ny dy ≤
      8192 * (n + gap + TotalWidth.width nx dx ny dy + 1) ^ 2 := by
  let w := TotalWidth.width nx dx ny dy
  let room := n + gap + w + 1
  have positive : 1 ≤ room := by unfold room; omega
  have nBound : n ≤ room := by unfold room; omega
  have gapBound : gap ≤ room := by unfold room; omega
  have widthBound : w ≤ room := by unfold room; omega
  have nxBound : (false :: nx).length ≤ room := by unfold room w TotalWidth.width; omega
  have dxBound : (false :: dx).length ≤ room := by unfold room w TotalWidth.width; omega
  have nyBound : (false :: ny).length ≤ room := by unfold room w TotalWidth.width; omega
  have dyBound : (false :: dy).length ≤ room := by unfold room w TotalWidth.width; omega
  have aBound : (PayloadFour.a memory nx).length ≤ room := nxBound
  have bBound : (PayloadFour.b memory dx).length ≤ room := dxBound
  have cBound : (PayloadFour.c memory ny).length ≤ room := nyBound
  have numCost : TotalWidth.numCost dx ny dy ≤ 2 * room + 23 := by
    unfold TotalWidth.numCost room w TotalWidth.width
    omega
  have firstCost : PayloadFour.firstCost n gap dx ny dy ≤ 12 * room + 123 := by
    unfold PayloadFour.firstCost
    omega
  have secondCost : PayloadFour.secondCost n gap memory nx ny dy ≤ 12 * room + 123 := by
    unfold PayloadFour.secondCost PayloadFour.a TotalWidth.denCost room w TotalWidth.width
    simp only [List.length_cons]
    omega
  have thirdCost : PayloadFour.thirdCost n gap memory nx dx dy ≤ 12 * room + 123 := by
    unfold PayloadFour.thirdCost PayloadFour.a PayloadFour.b TotalWidth.riskNumCost room w TotalWidth.width
    simp only [List.length_cons]
    omega
  have fourthCost : PayloadFour.fourthCost n gap memory nx dx ny ≤ 12 * room + 123 := by
    unfold PayloadFour.fourthCost PayloadFour.a PayloadFour.b PayloadFour.c room w TotalWidth.width
    simp only [List.length_cons]
    omega
  have copy1 := copy_fee_le nx (PayloadFour.firstCost n gap dx ny dy) room positive nxBound firstCost
  have copy2 := copy_fee_le dx (PayloadFour.secondCost n gap memory nx ny dy) room positive dxBound secondCost
  have copy3 := copy_fee_le ny (PayloadFour.thirdCost n gap memory nx dx dy) room positive nyBound thirdCost
  have copy4 := copy_fee_le dy (PayloadFour.fourthCost n gap memory nx dx ny) room positive dyBound fourthCost
  have linear : room ≤ room ^ 2 := by
    simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left room positive
  have one : 1 ≤ room ^ 2 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right positive (by decide : 0 ≤ 2)
  have init : 32 * n + 2 * gap + 2 * (false :: nx).length + TotalWidth.numCost dx ny dy + 104 ≤
      256 * room ^ 2 := by omega
  have next1 : 2 * (PayloadFour.a memory nx).length + 2 * (false :: dx).length +
      PayloadFour.secondCost n gap memory nx ny dy + 6 ≤ 256 * room ^ 2 := by omega
  have next2 : 2 * (PayloadFour.b memory dx).length + 2 * (false :: ny).length +
      PayloadFour.thirdCost n gap memory nx dx dy + 6 ≤ 256 * room ^ 2 := by omega
  have next3 : 2 * (PayloadFour.c memory ny).length + 2 * (false :: dy).length +
      PayloadFour.fourthCost n gap memory nx dx ny + 6 ≤ 256 * room ^ 2 := by omega
  have back : 2 * ((PayloadFour.a memory nx).length + (PayloadFour.b memory dx).length +
      (PayloadFour.c memory ny).length) + 27 ≤ 64 * room ^ 2 := by omega
  have clear : 11 ≤ 16 * room ^ 2 := by omega
  change PayloadFour.fee n gap memory nx dx ny dy ≤ 8192 * room ^ 2
  unfold PayloadFour.fee
  omega

theorem gap_scale_le (k w : Nat) :
    2 * w + k * w ^ 4 + 1 ≤ (k + 3) * (w + 1) ^ 4 := by
  have positive : 1 ≤ w + 1 := by omega
  have linear : w ≤ (w + 1) ^ 4 := by
    have h : w + 1 ≤ (w + 1) ^ 4 := by
      simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1 ≤ 4)
    exact (Nat.le_succ w).trans h
  have one : 1 ≤ (w + 1) ^ 4 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right positive (by decide : 0 ≤ 4)
  have fourth := Nat.mul_le_mul_left k (Nat.pow_le_pow_left (Nat.le_succ w) 4)
  nlinarith only [linear, one, fourth]

theorem quartic_fee_le (k memory : Nat) (nx dx ny dy : List Bool) :
    PayloadFour.fee (TotalWidth.width nx dx ny dy) (k * TotalWidth.width nx dx ny dy ^ 4) memory nx dx ny dy ≤
      (8192 * (k + 3) ^ 2) * (TotalWidth.width nx dx ny dy + 1) ^ 8 := by
  let w := TotalWidth.width nx dx ny dy
  have fee := fee_le w (k * w ^ 4) memory nx dx ny dy
  have scale := gap_scale_le k w
  have square := Nat.pow_le_pow_left scale 2
  have shape : ((k + 3) * (w + 1) ^ 4) ^ 2 = (k + 3) ^ 2 * (w + 1) ^ 8 := by ring
  rw [shape] at square
  change PayloadFour.fee w (k * w ^ 4) memory nx dx ny dy ≤ _
  change PayloadFour.fee w (k * w ^ 4) memory nx dx ny dy ≤ 8192 * (w + k * w ^ 4 + w + 1) ^ 2 at fee
  have rearranged : w + k * w ^ 4 + w + 1 = 2 * w + k * w ^ 4 + 1 := by omega
  rw [rearranged] at fee
  calc
    _ ≤ 8192 * (2 * w + k * w ^ 4 + 1) ^ 2 := fee
    _ ≤ 8192 * ((k + 3) ^ 2 * (w + 1) ^ 8) := Nat.mul_le_mul_left 8192 square
    _ = _ := by ring

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadCost
