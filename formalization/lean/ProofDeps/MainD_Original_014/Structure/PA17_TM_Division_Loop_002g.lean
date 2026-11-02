module

public import Structure.PA17_TM_Division_Loop_002a
public import Structure.PA17_TM_Division_Sub_001c
public import Common.PSTR_TM_CompareValue_056
public import Common.PSTR_TM_ShiftColumnTrace_066

/-! Arithmetic of the exact resident transformations used by finite control.
These are ghost descriptions of real tape changes, never machine inputs.
One source bit causes exactly one shift, at most one compare/subtract. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2200000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
open PSTRTMIncrement009 PSTRTMBinaryAdd024 PSTRTMCompareCode054

/-- This branch is read from the real nondestructive comparison's HALT label. -/
def residentEmit (zeroMode bit : Bool) (pairs : List (Bool × Bool)) : Bool :=
  if zeroMode then false
  else decide ((resultRelation 0 (PSTRTMShiftColumnCode065.shiftPairs bit pairs)).val ≠ 1)

def residentNext (zeroMode bit : Bool) (pairs : List (Bool × Bool)) : List (Bool × Bool) :=
  let shifted := PSTRTMShiftColumnCode065.shiftPairs bit pairs
  if residentEmit zeroMode bit pairs then PA17TMDivisionSub001.subPairs false shifted else shifted

/-- The quotient is retained LSB-first in the same archive cells. -/
def loopValues (zeroMode : Bool) : List Bool → List Bool → List (Bool × Bool) → List Bool × List (Bool × Bool)
  | [], quotient, resident => (quotient,resident)
  | bit :: later, quotient, resident =>
    loopValues zeroMode later (residentEmit zeroMode bit resident :: quotient) (residentNext zeroMode bit resident)

theorem compare_ge_iff (pairs : List (Bool × Bool)) :
    (resultRelation 0 pairs).val ≠ 1 ↔ secondValue pairs ≤ firstValue pairs := by
  rw [PSTRTMCompareValue056.resultRelation_classify]
  by_cases he : firstValue pairs = secondValue pairs
  · simp [PSTRTMCompareValue056.classify, he]
  · by_cases hl : firstValue pairs < secondValue pairs
    · have hn : ¬ secondValue pairs ≤ firstValue pairs := by omega
      simp [PSTRTMCompareValue056.classify, he, hl, hn]
    · have hle : secondValue pairs ≤ firstValue pairs := by omega
      simp [PSTRTMCompareValue056.classify, he, hl, hle]

theorem residentNext_length (zeroMode bit : Bool) (pairs : List (Bool × Bool)) :
    (residentNext zeroMode bit pairs).length = pairs.length := by
  unfold residentNext
  split <;> simp only [PA17TMDivisionSub001.subPairs_length, PSTRTMShiftColumnCode065.shiftPairs_length]

theorem residentNext_second (zeroMode bit : Bool) (pairs : List (Bool × Bool)) :
    secondValue (residentNext zeroMode bit pairs) = secondValue pairs := by
  unfold residentNext
  split <;> simp only [PA17TMDivisionSub001.secondValue_subPairs, PSTRTMShiftColumnCode065.secondValue_shiftPairs]

theorem shift_no_overflow (bit : Bool) (pairs : List (Bool × Bool))
    (room : 2 * firstValue pairs + bit.toNat < 2 ^ pairs.length) :
    PSTRTMShiftColumnCode065.finalCarry bit pairs = false ∧
      firstValue (PSTRTMShiftColumnCode065.shiftPairs bit pairs) = 2 * firstValue pairs + bit.toNat := by
  have hb := PSTRTMShiftColumnCode065.firstValue_shiftPairs bit pairs
  cases hc : PSTRTMShiftColumnCode065.finalCarry bit pairs
  · simp only [hc, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hb
    exact ⟨rfl,hb⟩
  · simp only [hc, Bool.toNat_true, Nat.mul_one] at hb
    omega

theorem residentEmit_correct (zeroMode bit : Bool) (pairs : List (Bool × Bool))
    (hz : zeroMode = decide (secondValue pairs = 0))
    (room : 2 * firstValue pairs + bit.toNat < 2 ^ pairs.length) :
    residentEmit zeroMode bit pairs = quotientBit (secondValue pairs) (firstValue pairs) bit := by
  have hs := (shift_no_overflow bit pairs room).2
  subst zeroMode
  by_cases hb : secondValue pairs = 0
  · simp [residentEmit, hb, quotientBit]
  · have hp : 0 < secondValue pairs := by omega
    simp [residentEmit, hb, quotientBit, hp, compare_ge_iff,
      PSTRTMShiftColumnCode065.secondValue_shiftPairs, hs]

theorem residentNext_correct (zeroMode bit : Bool) (pairs : List (Bool × Bool))
    (hz : zeroMode = decide (secondValue pairs = 0))
    (room : 2 * firstValue pairs + bit.toNat < 2 ^ pairs.length) (quotient : Nat) :
    (2 * quotient + (residentEmit zeroMode bit pairs).toNat, firstValue (residentNext zeroMode bit pairs)) =
      pushBit (secondValue pairs) bit (quotient,firstValue pairs) := by
  have he := residentEmit_correct zeroMode bit pairs hz room
  have hs := (shift_no_overflow bit pairs room).2
  have hb := PSTRTMShiftColumnCode065.secondValue_shiftPairs bit pairs
  unfold residentNext
  cases ht : residentEmit zeroMode bit pairs
  · simp only [ht, Bool.false_eq_true, ite_false, hs, pushBit, ← he]
  · have hg : secondValue (PSTRTMShiftColumnCode065.shiftPairs bit pairs) ≤
        firstValue (PSTRTMShiftColumnCode065.shiftPairs bit pairs) := by
      rw [hb,hs]
      have htrue : quotientBit (secondValue pairs) (firstValue pairs) bit = true := he.symm.trans ht
      have hboth : 0 < secondValue pairs ∧ secondValue pairs ≤ 2 * firstValue pairs + bit.toNat := by
        simpa only [quotientBit, decide_eq_true_eq] using htrue
      exact hboth.2
    have hx := (PA17TMDivisionSub001.subtraction_exact _ hg).2
    simp only [ht, ite_true, hx, hs, hb, pushBit, ← he]

theorem next_room_from_source (divisor : Nat) (higher : List Bool) (bit : Bool)
    (pairs : List (Bool × Bool)) (hr : firstValue pairs = (quotRem divisor higher).2)
    (hlen : (bit :: higher).length ≤ pairs.length) :
    2 * firstValue pairs + bit.toNat < 2 ^ pairs.length := by
  have hmod : firstValue pairs ≤ valueDigits higher := by
    rw [hr, quotRem_correct]
    exact Nat.mod_le _ _
  have hv := PSTRTMCanonical020.valueDigits_lt (bit :: higher)
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlen
  change Nat.bit bit (valueDigits higher) < 2 ^ (bit :: higher).length at hv
  rw [bit_value] at hv
  omega

theorem loopValues_length (zeroMode : Bool) (remaining quotient : List Bool) (resident : List (Bool × Bool)) :
    (loopValues zeroMode remaining quotient resident).1.length = remaining.length + quotient.length ∧
      (loopValues zeroMode remaining quotient resident).2.length = resident.length ∧
      secondValue (loopValues zeroMode remaining quotient resident).2 = secondValue resident := by
  induction remaining generalizing quotient resident with
  | nil => exact ⟨(Nat.zero_add quotient.length).symm,rfl,rfl⟩
  | cons bit later ih =>
    have hs := ih (residentEmit zeroMode bit resident :: quotient) (residentNext zeroMode bit resident)
    simp only [loopValues, List.length_cons, residentNext_length, residentNext_second] at hs ⊢
    exact ⟨by omega,hs.2⟩

/-- SAME quotient/remainder recurrence, including divisor0, under only the
internal tape-width room derived from the source length. -/
theorem loopValues_correct (divisor : Nat) (zeroMode : Bool) (remaining higher : List Bool)
    (resident : List (Bool × Bool)) (hz : zeroMode = decide (divisor = 0))
    (hb : secondValue resident = divisor) (hr : firstValue resident = (quotRem divisor higher).2)
    (hlen : remaining.length + higher.length ≤ resident.length) :
    (loopValues zeroMode remaining (quotientDigits divisor higher) resident).1 =
        quotientDigits divisor (remaining.reverse ++ higher) ∧
      firstValue (loopValues zeroMode remaining (quotientDigits divisor higher) resident).2 =
        (quotRem divisor (remaining.reverse ++ higher)).2 := by
  induction remaining generalizing higher resident with
  | nil =>
    change quotientDigits divisor higher = quotientDigits divisor higher ∧ firstValue resident = (quotRem divisor higher).2
    exact ⟨rfl,hr⟩
  | cons bit later ih =>
    have hroom := next_room_from_source divisor higher bit resident hr (by simp only [List.length_cons] at hlen ⊢; omega)
    have hem := residentEmit_correct zeroMode bit resident (by simpa only [hb] using hz) hroom
    have hn := residentNext_correct zeroMode bit resident (by simpa only [hb] using hz) hroom (quotRem divisor higher).1
    have hnr : firstValue (residentNext zeroMode bit resident) = (quotRem divisor (bit :: higher)).2 := by
      have heq := congrArg Prod.snd hn
      simpa only [hb,hr,quotRem] using heq
    have hq : residentEmit zeroMode bit resident :: quotientDigits divisor higher = quotientDigits divisor (bit :: higher) := by
      simp only [quotientDigits, hem, hb, hr]
    rw [loopValues,hq]
    have hs := ih (bit :: higher) (residentNext zeroMode bit resident) (by rw [residentNext_second,hb]) hnr
      (by rw [residentNext_length]; simp only [List.length_cons] at hlen ⊢; omega)
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hs

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
