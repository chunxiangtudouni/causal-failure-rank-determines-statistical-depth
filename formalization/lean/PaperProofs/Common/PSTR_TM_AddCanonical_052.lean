module
public import PaperProofs.Common.PSTR_TM_RawPack_045
public import PaperProofs.Common.PSTR_TM_Canonical_020
public import PaperProofs.Common.PSTR_TM_Arithmetic_008

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAddCanonical052
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009 PSTRTMBinaryAdd024 PSTRTMPackCode036 PSTRTMNatValue017

theorem digitPairs_values (first second : List Bool) :
    firstValue (digitPairs first second) = valueDigits first ∧
      secondValue (digitPairs first second) = valueDigits second := by
  induction first generalizing second with
  | nil =>
    induction second with
    | nil => simp [digitPairs, firstValue, secondValue, valueDigits]
    | cons b rest ih =>
      simp only [digitPairs]
      change Nat.bit false (firstValue (digitPairs [] rest)) = 0 ∧
        Nat.bit b (secondValue (digitPairs [] rest)) = Nat.bit b (valueDigits rest)
      rw [ih.1, ih.2]
      exact ⟨rfl,rfl⟩
  | cons a later ih =>
    cases second with
    | nil =>
      simp only [digitPairs]
      change Nat.bit a (firstValue (digitPairs later [])) = Nat.bit a (valueDigits later) ∧
        Nat.bit false (secondValue (digitPairs later [])) = 0
      rw [(ih []).1, (ih []).2]
      exact ⟨rfl,rfl⟩
    | cons b rest =>
      simp only [digitPairs]
      change Nat.bit a (firstValue (digitPairs later rest)) = Nat.bit a (valueDigits later) ∧
        Nat.bit b (secondValue (digitPairs later rest)) = Nat.bit b (valueDigits rest)
      rw [(ih rest).1, (ih rest).2]
      exact ⟨rfl,rfl⟩

theorem sumDigits_length_bounds (carry : Bool) (pairs : List (Bool × Bool)) :
    pairs.length ≤ (sumDigits carry pairs).length ∧ (sumDigits carry pairs).length ≤ pairs.length + 1 := by
  induction pairs generalizing carry with
  | nil => cases carry <;> simp [sumDigits]
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    have h := ih (carryBit carry a b)
    simpa only [sumDigits, List.length_cons] using
      And.intro (Nat.succ_le_succ h.1) (Nat.succ_le_succ h.2)

theorem sumDigits_extra_last (carry : Bool) (pairs : List (Bool × Bool))
    (extra : pairs.length < (sumDigits carry pairs).length) :
    (sumDigits carry pairs).getLast? = some true := by
  induction pairs generalizing carry with
  | nil =>
    cases carry with
    | false => simp [sumDigits] at extra
    | true => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    have ht : later.length < (sumDigits (carryBit carry a b) later).length := by
      simpa only [sumDigits, List.length_cons, Nat.add_lt_add_iff_right] using extra
    have hh := ih (carryBit carry a b) ht
    have hne : sumDigits (carryBit carry a b) later ≠ [] := by
      intro he
      simp [he] at ht
    rw [sumDigits, List.getLast?_cons_of_ne_nil hne]
    exact hh

theorem canonical_of_width (digits : List Bool) (width : digits.length = natBits (valueDigits digits)) :
    digits = rawPayload (valueDigits digits) := by
  apply List.ext_getElem
  · simpa only [rawPayload, List.length_ofFn] using width
  · intro i hi hj
    have he := testBit_valueDigits digits i
    rw [List.getI_eq_getElem _ hi] at he
    simpa only [rawPayload, List.getElem_ofFn] using he.symm

/-- Exact original canonical payload, including sum0=[false]. The actual
carry code's extra cell can occur only with a true highest bit; an unextended
sum has width at least the larger ORIGINAL operand's canonical width. -/
theorem sumDigits_rawPayload_eq (a b : Nat) :
    sumDigits false (digitPairs (rawPayload a) (rawPayload b)) = rawPayload (a + b) := by
  let pairs := digitPairs (rawPayload a) (rawPayload b)
  let output := sumDigits false pairs
  have hv := digitPairs_values (rawPayload a) (rawPayload b)
  have hvalue : valueDigits output = a + b := by
    simp only [output, pairs, sumDigits_value, hv.1, hv.2, valueDigits_rawPayload,
      Bool.toNat_false, Nat.add_zero]
  have hpair : pairs.length = max (natBits a) (natBits b) := by
    simp only [pairs, digitPairs_length, rawPayload, List.length_ofFn]
  have hpos : 0 < pairs.length := by
    rw [hpair]
    have ha : 0 < natBits a := by simp [natBits]
    exact lt_of_lt_of_le ha (Nat.le_max_left _ _)
  have bounds := sumDigits_length_bounds false pairs
  have hne : output ≠ [] := by
    intro he
    have hl := bounds.1
    change pairs.length ≤ output.length at hl
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega
  have hupper : natBits (valueDigits output) ≤ output.length :=
    PSTRTMArithmetic008.natBits_le_of_lt_pow _ _ (PSTRTMCanonical020.valueDigits_lt output)
      (List.length_pos_iff.mpr hne)
  have hlower : pairs.length ≤ natBits (valueDigits output) := by
    rw [hpair, hvalue]
    exact max_le (PSTRTMArithmetic008.natBits_mono (by omega : a ≤ a + b))
      (PSTRTMArithmetic008.natBits_mono (by omega : b ≤ a + b))
  have hwidth : output.length = natBits (valueDigits output) := by
    by_cases hextra : pairs.length < output.length
    · have hlast : output.getLast? = some true := sumDigits_extra_last false pairs hextra
      exact (PSTRTMCanonical020.canonical_width output hlast).symm
    · omega
  have hc := canonical_of_width output hwidth
  rw [hvalue] at hc
  exact hc

theorem rawWord_sum_eq (a b : Nat) :
    PSTRTMUnblockTrace019.rawWord (sumDigits false (digitPairs (rawPayload a) (rawPayload b))) = encodeNat (a + b) := by
  rw [sumDigits_rawPayload_eq]
  simp [PSTRTMUnblockTrace019.rawWord, rawPayload, encodeNat]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAddCanonical052
