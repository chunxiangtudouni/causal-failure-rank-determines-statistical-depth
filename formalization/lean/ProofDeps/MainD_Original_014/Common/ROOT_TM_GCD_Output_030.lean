module
public import Common.ROOT_TM_GCD_LoopValue_029

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDOutput030
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006 ROOTTMGCDDispatch018 ROOTTMGCDLift020 ROOTTMGCDLeg021 ROOTTMGCDPairStep019
local notation "AVal" => PSTRTMBinaryAdd024.firstValue
local notation "BVal" => PSTRTMBinaryAdd024.secondValue

def outputPairs (pairs : List Pair) : List Pair:=pairs.map ROOTTMGCDMap004.outputPair

theorem output_first_when_a_zero (pairs : List Pair) (ha : AVal pairs=0) :
    AVal (outputPairs pairs)=BVal pairs := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩:=pair
    have hz : Nat.bit a (AVal later)=0 := ha
    cases a
    · have hl : AVal later=0 := by simp only [Nat.bit,Bool.cond_false] at hz;omega
      have h:=ih hl
      change Nat.bit (false || b) (AVal (outputPairs later))=Nat.bit b (BVal later)
      rw [Bool.false_or,h]
    · simp [Nat.bit] at hz
theorem output_first_when_b_zero (pairs : List Pair) (hb : BVal pairs=0) :
    AVal (outputPairs pairs)=AVal pairs := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩:=pair
    have hz : Nat.bit b (BVal later)=0 := hb
    cases b
    · have hl : BVal later=0 := by simp only [Nat.bit,Bool.cond_false] at hz;omega
      have h:=ih hl
      change Nat.bit (a || false) (AVal (outputPairs later))=Nat.bit a (AVal later)
      rw [Bool.or_false,h]
    · simp [Nat.bit] at hz

theorem output_values (pairs : List Pair) (hz : AVal pairs=0 ∨ BVal pairs=0) :
    AVal (outputPairs pairs)=AVal pairs+BVal pairs ∧ BVal (outputPairs pairs)=0 := by
  refine ⟨?_,ROOTTMGCDMap004.secondValue_output pairs⟩
  cases hz with
  | inl ha => rw [output_first_when_a_zero pairs ha,ha,Nat.zero_add]
  | inr hb => rw [output_first_when_b_zero pairs hb,hb,Nat.add_zero]

def outputTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  (ROOTTMGCDMap004.residentMapTrace ROOTTMGCDMap004.outputPair (ROOTTMGCDCounter011.ones n) pairs suffix).map
    (lift (by decide : 36 ≤ 139) 18)
theorem output_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt 18 n pairs suffix) (outputTrace n pairs suffix) (cfgAt 19 n (outputPairs pairs) suffix) := by
  let archive:=ROOTTMGCDCounter011.ones n
  have run:=ROOTTMGCDMap004.residentMap_runsFrom ROOTTMGCDMap004.outputPair archive pairs suffix
  have hf : family 18=padMachine (by decide : 36 ≤ 139) (ROOTTMGCDMap004.residentMapMachine ROOTTMGCDMap004.outputPair) := rfl
  have hs:=phase_segment (by decide : 36 ≤ 139) 18 (ROOTTMGCDMap004.residentMapMachine ROOTTMGCDMap004.outputPair)
    hf _ _ _ run
  have ht:=phase_transfer (by decide : 36 ≤ 139) 18 19 (ROOTTMGCDMap004.residentMapMachine ROOTTMGCDMap004.outputPair)
    hf _ run.2.2.2 0 rfl
  exact ⟨lift (by decide : 36 ≤ 139) 18 (ROOTTMGCDMap004.residentMapFinal ROOTTMGCDMap004.outputPair archive pairs suffix),hs,ht⟩

theorem outputTrace_length (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (outputTrace n pairs suffix).length=14*pairs.length+6 := by
  simp only [outputTrace,List.length_map,ROOTTMGCDMap004.residentMap_length]

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDOutput030
