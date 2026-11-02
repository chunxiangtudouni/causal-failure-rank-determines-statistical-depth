module
public import Common.ROOT_TM_GCD_Codec_034

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDResident035
open PaperProofs.Common.Native.RationalControllerComputation
open ROOTTMGCDDispatch018 ROOTTMGCDLeg021 ROOTTMGCDPairStep019 ROOTTMGCDOutput030 ROOTTMGCDCodec034
local notation "AVal" => PSTRTMBinaryAdd024.firstValue
local notation "BVal" => PSTRTMBinaryAdd024.secondValue

def loopResult (pairs : List Pair) : ROOTTMGCDLoop028.Result:=
  ROOTTMGCDLoop028.loopData (ROOTTMGCDSteinMath009.rank (AVal pairs) (BVal pairs)) 0 pairs []
def restoreResult (pairs : List Pair) : ROOTTMGCDRestore032.Result:=
  ROOTTMGCDRestore032.restoreData (loopResult pairs).twos (outputPairs (loopResult pairs).pairs) []
def residentTrace (pairs : List Pair) : List (MachineState 3219) :=
  (loopResult pairs).trace++outputTrace (loopResult pairs).twos (loopResult pairs).pairs []++
    (restoreResult pairs).trace++codecTrace (restoreResult pairs).pairs
def residentFinal (pairs : List Pair) : MachineState 3219:=codecFinal (restoreResult pairs).pairs

theorem restoration_scale (pairs : List Pair) :
    2^(loopResult pairs).twos*AVal (outputPairs (loopResult pairs).pairs)=Nat.gcd (AVal pairs) (BVal pairs) := by
  have h:=ROOTTMGCDLoopValue029.loop_specs (ROOTTMGCDSteinMath009.rank (AVal pairs) (BVal pairs)) 0 pairs [] (le_refl _)
  have ht:=ROOTTMGCDLoopValue029.terminal_gcd_sum (loopResult pairs).pairs h.1
  have ho:=output_values (loopResult pairs).pairs h.1
  have hg:=h.2.2.2
  change 2^(loopResult pairs).twos*Nat.gcd (AVal (loopResult pairs).pairs) (BVal (loopResult pairs).pairs)=
    2^0*Nat.gcd (AVal pairs) (BVal pairs) at hg
  rw [ht,←ho.1,Nat.pow_zero,Nat.one_mul] at hg
  exact hg

theorem restoration_capacity (pairs : List Pair) :
    2^(loopResult pairs).twos*AVal (outputPairs (loopResult pairs).pairs)<2^(outputPairs (loopResult pairs).pairs).length := by
  have h:=ROOTTMGCDLoopValue029.loop_specs (ROOTTMGCDSteinMath009.rank (AVal pairs) (BVal pairs)) 0 pairs [] (le_refl _)
  have hl : (outputPairs (loopResult pairs).pairs).length=pairs.length := (List.length_map _).trans h.2.1
  rw [restoration_scale,hl]
  have hm : max (AVal pairs) (BVal pairs)<2^pairs.length := by
    have ha:=ROOTTMGCDLoopBound033.first_value_lt_width pairs
    have hb:=ROOTTMGCDLoopBound033.second_value_lt_width pairs
    omega
  exact lt_of_le_of_lt (ROOTTMGCDLoopValue029.gcd_le_max _ _) hm

theorem restored_gcd (pairs : List Pair) : AVal (restoreResult pairs).pairs=Nat.gcd (AVal pairs) (BVal pairs) := by
  have h:=ROOTTMGCDRestore032.restore_specs (loopResult pairs).twos (outputPairs (loopResult pairs).pairs) []
    (restoration_capacity pairs)
  exact h.1.trans (restoration_scale pairs)

/-- All actual phases execute and HALT with exact canonical gcd output.
This is a retained-column contract; original raw input and resource bounds
are proved separately, and are not assumed as arguments here. -/
theorem resident_runsFrom (pairs : List Pair) :
    PSTRTMSeq005.RunsFrom residentGcdMachine (cfgAt 0 0 pairs []) (residentTrace pairs) (residentFinal pairs) := by
  have h1:=ROOTTMGCDLoop028.loop_leg (ROOTTMGCDSteinMath009.rank (AVal pairs) (BVal pairs)) 0 pairs [] (le_refl _)
  have h2:=output_leg (loopResult pairs).twos (loopResult pairs).pairs []
  have h3:=ROOTTMGCDRestore032.restore_leg (loopResult pairs).twos (outputPairs (loopResult pairs).pairs) []
    (restoration_capacity pairs)
  have h4:=codec_runsFrom (restoreResult pairs).pairs
  exact finish_leg _ _ _ _ _ (Leg.append _ _ _ _ _ (Leg.append _ _ _ _ _ h1 h2) h3) h4

theorem resident_final_tape (pairs : List Pair) :
    (residentFinal pairs).Tape=Turing.Tape.mk₁ (encodeNat (Nat.gcd (AVal pairs) (BVal pairs))) := by
  rw [residentFinal,codec_final_tape,restored_gcd]

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDResident035
