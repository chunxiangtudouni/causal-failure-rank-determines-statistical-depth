module
public import Common.ROOT_TM_GCD_LoopValue_029

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDLoopBound033
open PaperProofs.Common.Native.RationalControllerComputation
open ROOTTMGCDLoop028 ROOTTMGCDPairStep019 ROOTTMGCDRoundLeg027 ROOTTMGCDDispatchLeg025
local notation "AVal" => PSTRTMBinaryAdd024.firstValue
local notation "BVal" => PSTRTMBinaryAdd024.secondValue

theorem loopTrace_length_le (fuel n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (loopData fuel n pairs suffix).trace.length ≤ 128*(pairs.length+n+fuel+1)*(fuel+1) := by
  induction fuel generalizing n pairs with
  | zero =>
    simp only [loopData,zeroTrace_length]
    omega
  | succ fuel ih =>
    by_cases hz : AVal pairs=0 ∨ BVal pairs=0
    · simp only [loopData,ite_eq_left hz,zeroTrace_length]
      have hm : 128*(pairs.length+n+1) ≤ 128*(pairs.length+n+(fuel+1)+1)*(fuel+1+1) := by
        calc
          _ ≤ 128*(pairs.length+n+(fuel+1)+1) := Nat.mul_le_mul_left 128 (by omega)
          _ ≤ 128*(pairs.length+n+(fuel+1)+1)*(fuel+1+1) := by
            exact Nat.le_mul_of_pos_right _ (by omega)
      have hs : 8*pairs.length+6 ≤ 128*(pairs.length+n+1) := by omega
      exact hs.trans hm
    · let n':=ROOTTMGCDSteinStep015.nextTwos (AVal pairs) (BVal pairs) n
      have hn : n' ≤ n+1 := by unfold n' ROOTTMGCDSteinStep015.nextTwos;split_ifs <;> omega
      have hr:=ih n' (nextPairs pairs)
      rw [next_length] at hr
      have hm : 128*(pairs.length+n'+fuel+1)*(fuel+1) ≤ 128*(pairs.length+n+fuel+2)*(fuel+1) :=
        Nat.mul_le_mul_right (fuel+1) (Nat.mul_le_mul_left 128 (by omega))
      have hc:=hr.trans hm
      have hs : (roundTrace n pairs suffix).length ≤ 128*(pairs.length+n+fuel+2) :=
        (roundTrace_length_le n pairs suffix).trans (Nat.mul_le_mul_left 128 (by omega))
      simp only [loopData,ite_eq_right hz,List.length_append]
      calc
        _ ≤ 128*(pairs.length+n+fuel+2)+128*(pairs.length+n+fuel+2)*(fuel+1) := Nat.add_le_add hs hc
        _ = 128*(pairs.length+n+(fuel+1)+1)*(fuel+1+1) := by ring

theorem first_value_lt_width (pairs : List Pair) : AVal pairs<2^pairs.length := by
  simpa only [PSTRTMBinaryAdd024.firstValue,List.length_map] using
    PSTRTMCanonical020.valueDigits_lt (pairs.map Prod.fst)
theorem second_value_lt_width (pairs : List Pair) : BVal pairs<2^pairs.length := by
  simpa only [PSTRTMBinaryAdd024.secondValue,List.length_map] using
    PSTRTMCanonical020.valueDigits_lt (pairs.map Prod.snd)
theorem rank_le_width (pairs : List Pair) : ROOTTMGCDSteinMath009.rank (AVal pairs) (BVal pairs) ≤ 2*pairs.length := by
  have ha:=Nat.size_le.mpr (first_value_lt_width pairs)
  have hb:=Nat.size_le.mpr (second_value_lt_width pairs)
  unfold ROOTTMGCDSteinMath009.rank
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDLoopBound033
