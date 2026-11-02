module

public import Structure.RootB23_Threshold_OriginalBridge_Code_001

/-! Original input bounds only. No width, B, room, branch, or bodyRun is
added to the caller. All constants are fixed before risk and depth. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace RootB23.Threshold.OriginalBridge
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticParse002
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

def scale (risk : Rat) (depth : Nat) : Nat :=
  (encode [.rational risk, .natural depth]).length + depth + 1

def width (risk : Rat) (depth : Nat) : Nat := fieldWidth (FactorSource.factorValue risk depth : Rat) risk

def timeCoefficient : Nat :=
  268435456 + (FixedConsumer.coefficient + 2 * FixedConsumer.k) * 16 ^ 8 + 300

theorem scale_positive (risk : Rat) (depth : Nat) : 1 ≤ scale risk depth := by
  unfold scale
  omega

theorem factor_positive (risk : Rat) (depth : Nat) : 0 < (FactorSource.factorValue risk depth : Rat) := by
  apply Nat.cast_pos.mpr
  unfold FactorSource.factorValue PSTRTMThresholdBadFactor226.factor
  omega

theorem product_positive (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    0 < (FactorSource.factorValue risk depth : Rat) * risk := mul_pos (factor_positive risk depth) hr

theorem original_width (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    width risk depth + 1 ≤ 16 * scale risk depth := by
  have factor := PSTRTMThresholdBadFactor226.factor_bits_le risk depth hr hd
  have original := PSTRTMThresholdRisk114.original_widths_le risk depth hr
  have unit : natBits 1 = 1 := by decide
  change natBits (FactorSource.factorValue risk depth) ≤ _ at factor
  unfold width fieldWidth
  simp only [numeratorDigits_length, denominatorDigits_length, Rat.num_natCast,
    Int.natAbs_natCast, Rat.den_natCast, unit]
  unfold scale
  omega

theorem original_b_width (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (FactorSource.bDigits risk depth).length ≤ 5 * scale risk depth := by
  have bits := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  simp only [FactorSource.bDigits, PSTRTMNatValue017.rawPayload, List.length_ofFn]
  unfold scale
  omega

theorem original_power (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (width risk depth + 1) ^ 8 ≤ 16 ^ 8 * scale risk depth ^ 8 := by
  have power := Nat.pow_le_pow_left (original_width risk depth hr hd) 8
  simpa only [Nat.mul_pow] using power

theorem original_linear_power (risk : Rat) (depth : Nat) :
    scale risk depth ≤ scale risk depth ^ 8 := by
  simpa only [pow_one] using Nat.pow_le_pow_right (scale_positive risk depth) (by decide : 1 ≤ 8)

theorem left_credit_bound (x y : Rat) (left right : Nat)
    (sum : left + right = Producer.left FixedConsumer.k x y + Spatial.MulCap.window x y
      (32 * fieldWidth x y + 512)) :
    left ≤ 2 * FixedConsumer.k * (fieldWidth x y + 1) ^ 8 := by
  have room : Spatial.MulCap.window x y (32 * fieldWidth x y + 512) ≤
      Producer.left FixedConsumer.k x y := by
    simpa only [Spatial.MulCap.window, Spatial.MulCap.time, Spatial.MulCap.inputLength,
      FixedConsumer.k, ProtectedConsumer.k] using
        Producer.left_room Spatial.MulCap.timeCoefficient 32 512 x y
  have leftSize : Producer.left FixedConsumer.k x y ≤ FixedConsumer.k * fieldWidth x y ^ 4 :=
    Nat.sub_le _ _
  have fourth : fieldWidth x y ^ 4 ≤ (fieldWidth x y + 1) ^ 8 :=
    (Nat.pow_le_pow_left (Nat.le_succ (fieldWidth x y)) 4).trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ fieldWidth x y + 1) (by decide : 4 ≤ 8))
  have scaled := Nat.mul_le_mul_left (2 * FixedConsumer.k) fourth
  have paid : left ≤ 2 * FixedConsumer.k * fieldWidth x y ^ 4 := by
    rw [Nat.mul_assoc]
    omega
  exact paid.trans scaled

theorem return_time_original (risk : Rat) (depth left right : Nat)
    (hr : 0 < risk) (hd : 1 ≤ depth)
    (sum : left + right = Producer.left FixedConsumer.k (FactorSource.factorValue risk depth : Rat) risk +
      Spatial.MulCap.window (FactorSource.factorValue risk depth : Rat) risk
        (32 * width risk depth + 512)) :
    ReturnActual.time risk depth risk left ≤
      (2 * FixedConsumer.k * 16 ^ 8 + 300) * scale risk depth ^ 8 := by
  have leftBound := left_credit_bound (FactorSource.factorValue risk depth : Rat) risk left right sum
  have power := original_power risk depth hr hd
  have linear := original_linear_power risk depth
  have unit : 1 ≤ scale risk depth ^ 8 := (scale_positive risk depth).trans linear
  have field := original_width risk depth hr hd
  have b := original_b_width risk depth hr hd
  have leftOriginal : left ≤ (2 * FixedConsumer.k * 16 ^ 8) * scale risk depth ^ 8 := by
    have scaled := Nat.mul_le_mul_left (2 * FixedConsumer.k) power
    change left ≤ 2 * FixedConsumer.k * (width risk depth + 1) ^ 8 at leftBound
    exact leftBound.trans (by simpa only [Nat.mul_assoc] using scaled)
  have fieldOriginal : 10 * width risk depth ≤ 160 * scale risk depth ^ 8 := by
    have fieldScale : width risk depth ≤ 16 * scale risk depth := by omega
    have toPower := Nat.mul_le_mul_left 16 linear
    have scaled := Nat.mul_le_mul_left 10 (fieldScale.trans toPower)
    simpa only [← Nat.mul_assoc] using scaled
  have bOriginal : 2 * (FactorSource.bDigits risk depth).length ≤ 10 * scale risk depth ^ 8 := by
    have scaled := Nat.mul_le_mul_left 2 (b.trans (Nat.mul_le_mul_left 5 linear))
    simpa only [← Nat.mul_assoc] using scaled
  have fixedOriginal : 96 ≤ 96 * scale risk depth ^ 8 := by omega
  unfold ReturnActual.time
  change left + 10 * width risk depth + 2 * (FactorSource.bDigits risk depth).length + 96 ≤ _
  have combined := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add leftOriginal fieldOriginal) bOriginal) fixedOriginal
  calc
    _ ≤ (2 * FixedConsumer.k * 16 ^ 8) * scale risk depth ^ 8 +
        160 * scale risk depth ^ 8 + 10 * scale risk depth ^ 8 + 96 * scale risk depth ^ 8 := combined
    _ ≤ _ := by rw [Nat.add_mul]; omega

end RootB23.Threshold.OriginalBridge
