module
public import Structure.PA17_TM_RatArithmetic_Outer_025b

/-! Cost of the actual counted-loop trace. This does not instantiate the
body contract or replace any execution/physical-window proof. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025

theorem linear_loopCost_le (a b growth h n : Nat) :
    loopCost (fun n => a*n+b) growth h n ≤
      (h+1)*(2*h+a*(n+growth*h)+b+16) := by
  induction h generalizing n with
  | zero => simp [loopCost]
  | succ h ih =>
    have ht := ih (n+growth)
    have index : (n+growth)+growth*h=n+growth*(h+1) := by
      rw [Nat.mul_succ]
      omega
    rw [index] at ht
    let q := 2*h+a*(n+growth*(h+1))+b+16
    have hm : a*n≤a*(n+growth*(h+1)) :=
      Nat.mul_le_mul_left a (by omega)
    have head : 2*h+16+(a*n+b)≤q := by dsimp [q];omega
    change 2*h+16+(a*n+b)+loopCost (fun n => a*n+b) growth h (n+growth) ≤ _
    calc
      _ ≤ q+(h+1)*q := Nat.add_le_add head ht
      _ = (h+2)*q := by ring
      _ ≤ (h+2)*(q+2) := Nat.mul_le_mul_left _ (by omega)
      _ = (h+1+1)*(2*(h+1)+a*(n+growth*(h+1))+b+16) := by dsimp [q];ring

def passFee (k width n : Nat) : Nat :=
  width*(2*n+(2*k+4)*width+4*k+64)+48

theorem passFee_linear (k width n : Nat) :
    passFee k width n=(2*width)*n+(width*((2*k+4)*width+4*k+64)+48) := by
  unfold passFee
  ring

theorem allocation_loopCost_le (k width : Nat) :
    loopCost (passFee k width) (k*width) width 0 ≤
      (16*k+256)*(width+1)^4 := by
  have fee : passFee k width=
      fun n => (2*width)*n+(width*((2*k+4)*width+4*k+64)+48) := by
    funext n
    exact passFee_linear k width n
  rw [fee]
  have hb := linear_loopCost_le (2*width)
    (width*((2*k+4)*width+4*k+64)+48) (k*width) width 0
  have hp : (width+1)*(2*width+(2*width)*(0+(k*width)*width)+
      (width*((2*k+4)*width+4*k+64)+48)+16) ≤
      (16*k+256)*(width+1)^4 := by
    nlinarith [Nat.zero_le (k*width^4),Nat.zero_le (k*width^3),
      Nat.zero_le (k*width^2),Nat.zero_le (k*width),
      Nat.zero_le (width^4),Nat.zero_le (width^3),Nat.zero_le (width^2)]
  exact hb.trans hp

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025
