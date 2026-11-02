module
public import Common.ROOT_TM_GCD_Resident_035

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDResidentBound036
open PaperProofs.Common.Native.RationalControllerComputation
open ROOTTMGCDPairStep019 ROOTTMGCDResident035 ROOTTMGCDOutput030 ROOTTMGCDCodec034
local notation "AVal" => PSTRTMBinaryAdd024.firstValue
local notation "BVal" => PSTRTMBinaryAdd024.secondValue

theorem loop_width (pairs : List Pair) : (loopResult pairs).pairs.length=pairs.length :=
  (ROOTTMGCDLoopValue029.loop_specs (ROOTTMGCDSteinMath009.rank (AVal pairs) (BVal pairs)) 0 pairs [] (le_refl _)).2.1
theorem loop_twos_le (pairs : List Pair) : (loopResult pairs).twos ≤ 2*pairs.length := by
  have h : (loopResult pairs).twos ≤ 0+ROOTTMGCDSteinMath009.rank (AVal pairs) (BVal pairs) :=
    (ROOTTMGCDLoopValue029.loop_specs (ROOTTMGCDSteinMath009.rank (AVal pairs) (BVal pairs)) 0 pairs [] (le_refl _)).2.2.1
  have hr:=ROOTTMGCDLoopBound033.rank_le_width pairs
  omega
theorem output_width (pairs : List Pair) : (outputPairs (loopResult pairs).pairs).length=pairs.length :=
  (List.length_map _).trans (loop_width pairs)
theorem restore_width (pairs : List Pair) : (restoreResult pairs).pairs.length=pairs.length :=
  (ROOTTMGCDRestore032.restore_specs (loopResult pairs).twos (outputPairs (loopResult pairs).pairs) []
    (restoration_capacity pairs)).2.2.trans (output_width pairs)

theorem resident_length_le (pairs : List Pair) : (residentTrace pairs).length ≤ 4096*(pairs.length+1)^2 := by
  have hr:=ROOTTMGCDLoopBound033.rank_le_width pairs
  have hl:=ROOTTMGCDLoopBound033.loopTrace_length_le (ROOTTMGCDSteinMath009.rank (AVal pairs) (BVal pairs)) 0 pairs []
  have hml : 128*(pairs.length+0+ROOTTMGCDSteinMath009.rank (AVal pairs) (BVal pairs)+1)*
      (ROOTTMGCDSteinMath009.rank (AVal pairs) (BVal pairs)+1) ≤ 128*(3*pairs.length+1)*(2*pairs.length+1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 128 (by omega)) (by omega)
  have hl' : (loopResult pairs).trace.length ≤ 128*(3*pairs.length+1)*(2*pairs.length+1) := hl.trans hml
  have hk:=loop_twos_le pairs
  have hs:=ROOTTMGCDRestore032.restoreTrace_length_le (loopResult pairs).twos (outputPairs (loopResult pairs).pairs) []
  rw [output_width] at hs
  have hms : 64*(pairs.length+(loopResult pairs).twos+1)*((loopResult pairs).twos+1) ≤
      64*(3*pairs.length+1)*(2*pairs.length+1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 64 (by omega)) (by omega)
  have hs' : (restoreResult pairs).trace.length ≤ 64*(3*pairs.length+1)*(2*pairs.length+1) := hs.trans hms
  have ho:=outputTrace_length (loopResult pairs).twos (loopResult pairs).pairs []
  rw [loop_width] at ho
  have hc:=codecTrace_length_le (restoreResult pairs).pairs
  rw [restore_width] at hc
  simp only [residentTrace,List.length_append,ho]
  nlinarith

theorem resident_visitedSpace_le (pairs : List Pair) (inputLength : Nat) :
    visitedSpace ROOTTMGCDDispatch018.residentGcdMachine inputLength (residentTrace pairs) ≤
      inputLength+8192*(pairs.length+1)^2+1 := by
  have h:=PSTRTMTrace002.visitedSpace_le ROOTTMGCDDispatch018.residentGcdMachine inputLength (residentTrace pairs)
  have ht:=resident_length_le pairs
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDResidentBound036
