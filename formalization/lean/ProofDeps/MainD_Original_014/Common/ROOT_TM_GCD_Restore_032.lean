module
public import Common.ROOT_TM_GCD_RestoreLeg_031
public import Common.PSTR_TM_B1Invariant_075

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDRestore032
open PaperProofs.Common.Native.RationalControllerComputation
open ROOTTMGCDDispatch018 ROOTTMGCDLeg021 ROOTTMGCDPairStep019 ROOTTMGCDRestoreLeg031
local notation "AVal" => PSTRTMBinaryAdd024.firstValue
local notation "BVal" => PSTRTMBinaryAdd024.secondValue
local notation "shift" => PSTRTMShiftColumnCode065.shiftPairs false

structure Result where
  trace : List (MachineState 3219)
  pairs : List Pair
def restoreData : Nat → List Pair → List Bool → Result
  | 0,pairs,suffix => ⟨popZeroTrace pairs suffix,pairs⟩
  | n+1,pairs,suffix =>
    let later:=restoreData n (shift pairs) suffix
    ⟨restoreStepTrace n pairs suffix++later.trace,later.pairs⟩

theorem first_shift_capacity (n : Nat) (pairs : List Pair)
    (hcap : 2^(n+1)*AVal pairs<2^pairs.length) :
    2*AVal pairs<2^pairs.length := by
  have hp : 1 ≤ 2^n:=Nat.one_le_two_pow
  have hm:=Nat.mul_le_mul_right (2*AVal pairs) hp
  have hf : 2^n*(2*AVal pairs)<2^pairs.length := by
    simpa only [Nat.pow_succ,Nat.mul_assoc] using hcap
  simpa only [Nat.one_mul] using lt_of_le_of_lt hm hf

/-- Actual common-power restoration, controlled by physical counter pop.
The capacity fact comes from original gcd preservation and input width. -/
theorem restore_leg (n : Nat) (pairs : List Pair) (suffix : List Bool)
    (hcap : 2^n*AVal pairs<2^pairs.length) :
    Leg (cfgAt 19 n pairs suffix) (restoreData n pairs suffix).trace
      (cfgAt 22 0 (restoreData n pairs suffix).pairs suffix) := by
  induction n generalizing pairs with
  | zero => exact pop_zero_leg pairs suffix
  | succ n ih =>
    have hc:=PSTRTMB1Invariant075.noOverflow_of_double_lt pairs (first_shift_capacity n pairs hcap)
    have hv:=PSTRTMB1Invariant075.shifted_value_noOverflow pairs hc
    have hnext : 2^n*AVal (shift pairs)<2^(shift pairs).length := by
      rw [hv,PSTRTMShiftColumnCode065.shiftPairs_length]
      simpa only [Nat.pow_succ,Nat.mul_assoc] using hcap
    exact Leg.append _ _ _ _ _ (restoreStep_leg n pairs suffix hc) (ih (shift pairs) hnext)

theorem restore_specs (n : Nat) (pairs : List Pair) (suffix : List Bool)
    (hcap : 2^n*AVal pairs<2^pairs.length) :
    AVal (restoreData n pairs suffix).pairs=2^n*AVal pairs ∧
    BVal (restoreData n pairs suffix).pairs=BVal pairs ∧
    (restoreData n pairs suffix).pairs.length=pairs.length := by
  induction n generalizing pairs with
  | zero => simp only [restoreData,Nat.pow_zero,Nat.one_mul,and_self]
  | succ n ih =>
    have hc:=PSTRTMB1Invariant075.noOverflow_of_double_lt pairs (first_shift_capacity n pairs hcap)
    have hv:=PSTRTMB1Invariant075.shifted_value_noOverflow pairs hc
    have hnext : 2^n*AVal (shift pairs)<2^(shift pairs).length := by
      rw [hv,PSTRTMShiftColumnCode065.shiftPairs_length]
      simpa only [Nat.pow_succ,Nat.mul_assoc] using hcap
    have hr:=ih (shift pairs) hnext
    simpa only [restoreData,hv,Nat.pow_succ,Nat.mul_assoc,PSTRTMShiftColumnCode065.secondValue_shiftPairs,
      PSTRTMShiftColumnCode065.shiftPairs_length] using hr

theorem restoreTrace_length_le (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (restoreData n pairs suffix).trace.length ≤ 64*(pairs.length+n+1)*(n+1) := by
  induction n generalizing pairs with
  | zero =>
    change 5 ≤ 64*(pairs.length+0+1)*(0+1)
    omega
  | succ n ih =>
    have hr:=ih (shift pairs)
    rw [PSTRTMShiftColumnCode065.shiftPairs_length] at hr
    simp only [restoreData,List.length_append]
    rw [restoreStepTrace_length]
    nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDRestore032
