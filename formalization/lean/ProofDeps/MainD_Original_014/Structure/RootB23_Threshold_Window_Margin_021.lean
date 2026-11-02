module

public import Structure.RootB23_Threshold_Window_BareReserve_015

/-! The constant is chosen before all inputs. It covers the whole callee
window and a linear downstream reserve, including the three cells spent by
the agreed far-payload/count2 layout. This is arithmetic for that physical
caller obligation, not an alternative original-input room premise. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.Margin

def coefficient (callee linear constant : Nat) : Nat := 1296 * callee + linear + constant + 37

theorem exact_window_covered (callee linear constant w : Nat) (widthPositive : 4 ≤ w) :
    callee * (2 * w + 15) ^ 4 + 2 * (2 * w + 14) + (linear * w + constant) + 2 ≤
      coefficient callee linear constant * w ^ 4 - 3 := by
  have positive : 1 ≤ w := by omega
  have input : 2 * w + 15 ≤ 6 * w := by omega
  have power := Nat.pow_le_pow_left input 4
  have main := Nat.mul_le_mul_left callee power
  have mainBound : callee * (2 * w + 15) ^ 4 ≤ 1296 * callee * w ^ 4 := by
    nlinarith only [main]
  have linearPower : w ≤ w ^ 4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1 ≤ 4)
  have onePower : 1 ≤ w ^ 4 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right positive (by decide : 0 ≤ 4)
  have growing := Nat.mul_le_mul_left (linear + 4) linearPower
  have fixed := Nat.mul_le_mul_left (constant + 33) onePower
  have total : callee * (2 * w + 15) ^ 4 + 2 * (2 * w + 14) +
      (linear * w + constant) + 2 + 3 ≤ coefficient callee linear constant * w ^ 4 := by
    unfold coefficient
    nlinarith
  omega

theorem rational_width_at_least_four (x y : Rat) :
    4 ≤ PA17TMRatArithmeticParse002.fieldWidth x y := by
  have xWidth := PA17TMRatArithmeticParse002.field_widths_positive x
  have yWidth := PA17TMRatArithmeticParse002.field_widths_positive y
  unfold PA17TMRatArithmeticParse002.fieldWidth
  omega

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.Margin
