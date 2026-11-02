module
public import Common.PSTR_TM_CompareTrace_055
public import Common.PSTR_TM_AddCanonical_052
public import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareValue056
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMCompareCode054 PSTRTMBinaryAdd024

def digitRelation (a b : Bool) : Fin 3 := update 0 a b
def combine (higher lower : Fin 3) : Fin 3 := if higher.val = 0 then lower else higher
def classify (a b : Nat) : Fin 3 := if a = b then 0 else if a < b then 1 else 2
def resultLe (relation : Fin 3) : Bool := decide (relation.val ≠ 2)

theorem update_combine (relation : Fin 3) (a b : Bool) :
    update relation a b = combine (digitRelation a b) relation := by
  fin_cases relation <;> cases a <;> cases b <;> rfl

theorem combine_assoc (a b c : Fin 3) : combine (combine a b) c = combine a (combine b c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

theorem combine_zero_right (relation : Fin 3) : combine relation 0 = relation := by
  fin_cases relation <;> rfl

/-- Folded actual finite control keeps the old lower-bit relation only
when every newly-read higher digit pair is equal. -/
theorem resultRelation_combine (relation : Fin 3) (pairs : List (Bool × Bool)) :
    resultRelation relation pairs = combine (resultRelation 0 pairs) relation := by
  induction pairs generalizing relation with
  | nil => simp [resultRelation_nil, combine]
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    calc
      resultRelation relation ((a,b) :: later) = resultRelation (update relation a b) later := resultRelation_cons _ _ _ _
      _ = combine (resultRelation 0 later) (update relation a b) := ih _
      _ = combine (resultRelation 0 later) (combine (digitRelation a b) relation) := by rw [update_combine]
      _ = combine (combine (resultRelation 0 later) (digitRelation a b)) relation := (combine_assoc _ _ _).symm
      _ = combine (resultRelation (digitRelation a b) later) relation := by rw [ih (digitRelation a b)]
      _ = combine (resultRelation 0 ((a,b) :: later)) relation := by rw [resultRelation_cons]; rfl

theorem classify_bit (a b : Bool) (x y : Nat) :
    classify (Nat.bit a x) (Nat.bit b y) = combine (classify x y) (digitRelation a b) := by
  by_cases hlt : x < y
  · have hb := Nat.bit_lt_bit a b hlt
    have hne : x ≠ y := Nat.ne_of_lt hlt
    have hbn : Nat.bit a x ≠ Nat.bit b y := Nat.ne_of_lt hb
    simp [classify, hne, hlt, hbn, hb, combine]
  · by_cases he : x = y
    · subst y
      simp only [Nat.bit]
      cases a <;> cases b <;> simp [classify, combine, digitRelation, update]
    · have hgt : y < x := by omega
      have hb := Nat.bit_lt_bit b a hgt
      have hbn : Nat.bit a x ≠ Nat.bit b y := by omega
      have hblt : ¬Nat.bit a x < Nat.bit b y := by omega
      simp [classify, he, hlt, hbn, hblt, combine]

theorem resultRelation_classify (pairs : List (Bool × Bool)) :
    resultRelation 0 pairs = classify (firstValue pairs) (secondValue pairs) := by
  induction pairs with
  | nil => simp [resultRelation_nil, firstValue, secondValue, PSTRTMIncrement009.valueDigits, classify]
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [resultRelation_cons, resultRelation_combine, ih]
    change combine (classify (firstValue later) (secondValue later)) (digitRelation a b) =
      classify (Nat.bit a (firstValue later)) (Nat.bit b (secondValue later))
    exact (classify_bit a b _ _).symm

theorem classify_le_iff (a b : Nat) : (classify a b).val ≠ 2 ↔ a ≤ b := by
  by_cases he : a = b
  · subst b
    simp [classify]
  · by_cases hl : a < b
    · have hle : a ≤ b := Nat.le_of_lt hl
      simp [classify, he, hl, hle]
    · have hn : ¬a ≤ b := by omega
      simp [classify, he, hl, hn]

theorem resultRelation_le_iff (pairs : List (Bool × Bool)) :
    (resultRelation 0 pairs).val ≠ 2 ↔ firstValue pairs ≤ secondValue pairs := by
  rw [resultRelation_classify, classify_le_iff]

theorem original_le_iff (a b : Nat) :
    (resultRelation 0 (PSTRTMPackCode036.digitPairs (PSTRTMNatValue017.rawPayload a)
      (PSTRTMNatValue017.rawPayload b))).val ≠ 2 ↔ a ≤ b := by
  rw [resultRelation_le_iff]
  have hv := PSTRTMAddCanonical052.digitPairs_values (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)
  rw [hv.1, hv.2, PSTRTMNatValue017.valueDigits_rawPayload, PSTRTMNatValue017.valueDigits_rawPayload]

theorem original_resultLe (a b : Nat) :
    resultLe (resultRelation 0 (PSTRTMPackCode036.digitPairs (PSTRTMNatValue017.rawPayload a)
      (PSTRTMNatValue017.rawPayload b))) = decide (a ≤ b) := by
  by_cases h : a ≤ b
  · have hr := (original_le_iff a b).mpr h
    simp [resultLe, hr, h]
  · have hr : ¬(resultRelation 0 (PSTRTMPackCode036.digitPairs (PSTRTMNatValue017.rawPayload a)
        (PSTRTMNatValue017.rawPayload b))).val ≠ 2 := fun hh => h ((original_le_iff a b).mp hh)
    simp [resultLe, hr, h]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareValue056
