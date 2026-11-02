module
public import Common.ROOT_TM_GCD_ZeroTrace_007

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDZeroValue008
open PaperProofs.Common.Native.RationalControllerComputation
open ROOTTMGCDZero006

theorem control_specs (a b : Bool) : seenA (control a b)=a ∧ seenB (control a b)=b := by
  cases a <;> cases b <;> exact ⟨rfl,rfl⟩

theorem control_eta (r : Fin 4) : control (seenA r) (seenB r)=r := by
  fin_cases r <;> rfl

theorem update_specs (r : Fin 4) (a b : Bool) :
    seenA (update r a b)=(seenA r || a) ∧ seenB (update r a b)=(seenB r || b) :=
  control_specs _ _

theorem result_seenA (r : Fin 4) (pairs : List (Bool × Bool)) :
    seenA (resultControl r pairs)=(seenA r || pairs.any Prod.fst) := by
  induction pairs generalizing r with
  | nil => simp only [resultControl_nil,List.any_nil,Bool.or_false]
  | cons pair later ih =>
    obtain ⟨a,b⟩:=pair
    rw [resultControl_cons,ih,(update_specs r a b).1]
    simp only [List.any_cons,Bool.or_assoc]

theorem result_seenB (r : Fin 4) (pairs : List (Bool × Bool)) :
    seenB (resultControl r pairs)=(seenB r || pairs.any Prod.snd) := by
  induction pairs generalizing r with
  | nil => simp only [resultControl_nil,List.any_nil,Bool.or_false]
  | cons pair later ih =>
    obtain ⟨a,b⟩:=pair
    rw [resultControl_cons,ih,(update_specs r a b).2]
    simp only [List.any_cons,Bool.or_assoc]

theorem anyA_value (pairs : List (Bool × Bool)) :
    pairs.any Prod.fst=decide (PSTRTMBinaryAdd024.firstValue pairs≠0) := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩:=pair
    change (a || later.any Prod.fst)=decide (Nat.bit a (PSTRTMBinaryAdd024.firstValue later)≠0)
    rw [ih]
    cases a <;> simp [Nat.bit]

theorem anyB_value (pairs : List (Bool × Bool)) :
    pairs.any Prod.snd=decide (PSTRTMBinaryAdd024.secondValue pairs≠0) := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩:=pair
    change (b || later.any Prod.snd)=decide (Nat.bit b (PSTRTMBinaryAdd024.secondValue later)≠0)
    rw [ih]
    cases b <;> simp [Nat.bit]

/-- The branch facts are proved from the actually computed finite HALT
control, including all-zero columns and empty-width operands. -/
theorem actual_nonzero (pairs : List (Bool × Bool)) :
    seenA (resultControl 0 pairs)=decide (PSTRTMBinaryAdd024.firstValue pairs≠0) ∧
    seenB (resultControl 0 pairs)=decide (PSTRTMBinaryAdd024.secondValue pairs≠0) := by
  constructor
  · rw [result_seenA,show seenA 0=false from rfl,Bool.false_or,anyA_value]
  · rw [result_seenB,show seenB 0=false from rfl,Bool.false_or,anyB_value]

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDZeroValue008
