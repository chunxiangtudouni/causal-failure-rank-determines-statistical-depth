module
public import Common.ROOT_TM_GCD_DispatchLeg_025

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDControlValue026
open PaperProofs.Common.Native.RationalControllerComputation
open ROOTTMGCDDispatchLeg025 ROOTTMGCDPairStep019
local notation "AVal" => PSTRTMBinaryAdd024.firstValue
local notation "BVal" => PSTRTMBinaryAdd024.secondValue

theorem nonzero_control (pairs : List Pair) (ha : AVal pairs≠0) (hb : BVal pairs≠0) :
    ROOTTMGCDZero006.resultControl 0 pairs=3 := by
  let r:=ROOTTMGCDZero006.resultControl 0 pairs
  have h:=ROOTTMGCDZeroValue008.actual_nonzero pairs
  have h1 : ROOTTMGCDZero006.seenA r=true := by simpa [ha] using h.1
  have h2 : ROOTTMGCDZero006.seenB r=true := by simpa [hb] using h.2
  change r=3
  rw [←ROOTTMGCDZeroValue008.control_eta r,h1,h2]
  rfl

theorem nonzero_pairs (pairs : List Pair) (ha : AVal pairs≠0) : pairs≠[] := by
  intro h
  subst pairs
  exact ha rfl

theorem zero_control_not_three (pairs : List Pair) (hz : AVal pairs=0 ∨ BVal pairs=0) :
    (ROOTTMGCDZero006.resultControl 0 pairs).val≠3 := by
  have h:=ROOTTMGCDZeroValue008.actual_nonzero pairs
  intro hr
  have he : ROOTTMGCDZero006.resultControl 0 pairs=3 := Fin.ext hr
  cases hz with
  | inl ha =>
    have hc:=h.1
    rw [he,ha] at hc
    have ht : ROOTTMGCDZero006.seenA 3=true := rfl
    rw [ht] at hc
    simp at hc
  | inr hb =>
    have hc:=h.2
    rw [he,hb] at hc
    have ht : ROOTTMGCDZero006.seenB 3=true := rfl
    rw [ht] at hc
    simp at hc

theorem parity_mod (a b : Bool) (later : List Pair) :
    AVal ((a,b)::later)%2=a.toNat ∧ BVal ((a,b)::later)%2=b.toNat := by
  change (Nat.bit a (AVal later))%2=a.toNat ∧ (Nat.bit b (BVal later))%2=b.toNat
  cases a <;> cases b <;> simp [Nat.bit]

theorem compare_less_iff (pairs : List Pair) :
    (PSTRTMCompareCode054.resultRelation 0 pairs).val=1 ↔ AVal pairs<BVal pairs := by
  rw [PSTRTMCompareValue056.resultRelation_classify]
  by_cases he : AVal pairs=BVal pairs
  · simp [PSTRTMCompareValue056.classify,he]
  · by_cases hl : AVal pairs<BVal pairs <;> simp [PSTRTMCompareValue056.classify,he,hl]

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDControlValue026
