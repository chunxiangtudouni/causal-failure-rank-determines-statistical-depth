module
public import Structure.PA17_TM_RatArithmetic_WideCache_045a

/-! A fixed allocation constant is chosen before all actual arguments.
The scale hypothesis is a caller size invariant, not a field added to the
original tape. The actual counted allocator, not this theorem, produces W². -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWideCache045

open PA17TMRatArithmeticNativeCache030

def allocationK : Nat := 524320

theorem allocationK_pos : 0<allocationK := by decide

theorem window_le_allocated (a b width : Nat) (hw : 1≤width)
    (size : scale a b≤4*width) : window a b≤allocationK*width^2 := by
  have squared := Nat.pow_le_pow_left size 2
  have linear : width≤width^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left width hw
  unfold window allocationK
  nlinarith

theorem allocated_room (a b width : Nat) (hw : 1≤width) (size : scale a b≤4*width) :
    window a b-2≤allocationK*width^2 :=
  (Nat.sub_le (window a b) 2).trans (window_le_allocated a b width hw size)

theorem new_gap_bound (a b width newGap : Nat) (hw : 1≤width)
    (size : scale a b≤4*width)
    (actualGap : newGap≤allocationK*width^2+window a b) :
    newGap≤2*allocationK*width^2 := by
  have budget := window_le_allocated a b width hw size
  nlinarith

theorem add_allocated_runsFrom (a b width : Nat) (archive : List Bool) (hw : 1≤width)
    (size : scale a b≤4*width) :
    WideCacheResult PSTRTMNativeAdd053.nativeAddMachine a b (a+b) archive (allocationK*width^2) :=
  add_wide_runsFrom a b _ archive (allocated_room a b width hw size)

theorem sub_allocated_runsFrom (a b width : Nat) (archive : List Bool) (hw : 1≤width)
    (size : scale a b≤4*width) :
    WideCacheResult PA17TMRatArithmeticSub016.nativeSubMachine a b (a-b) archive (allocationK*width^2) :=
  sub_wide_runsFrom a b _ archive (allocated_room a b width hw size)

theorem mul_allocated_runsFrom (a b width : Nat) (archive : List Bool) (hw : 1≤width)
    (size : scale a b≤4*width) :
    WideCacheResult PSTRTMNativeMul112.nativeMulMachine a b (a*b) archive (allocationK*width^2) :=
  mul_wide_runsFrom a b _ archive (allocated_room a b width hw size)

theorem gcd_allocated_runsFrom (a b width : Nat) (archive : List Bool) (hw : 1≤width)
    (size : scale a b≤4*width) :
    WideCacheResult ROOTTMGCDDispatch018.nativeGcdMachine a b (Nat.gcd a b) archive (allocationK*width^2) :=
  gcd_wide_runsFrom a b _ archive (allocated_room a b width hw size)

theorem quotient_allocated_runsFrom (a b width : Nat) (archive : List Bool) (hw : 1≤width)
    (size : scale a b≤4*width) :
    WideCacheResult PA17TMDivisionFull012.quotientMachine a b (a/b) archive (allocationK*width^2) :=
  quotient_wide_runsFrom a b _ archive (allocated_room a b width hw size)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWideCache045
