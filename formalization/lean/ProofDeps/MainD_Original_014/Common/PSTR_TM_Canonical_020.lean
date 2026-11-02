module
public import Common.PSTR_TM_UnblockTrace_019

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCanonical020
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009 PSTRTMNatValue017 PSTRTMUnblockTrace019

theorem bump_ne_nil (digits : List Bool) : bumpDigits digits ≠ [] := by
  cases digits with
  | nil => simp [bumpDigits]
  | cons bit later => cases bit <;> simp [bumpDigits]

theorem valueDigits_lt (digits : List Bool) : valueDigits digits < 2 ^ digits.length := by
  induction digits with
  | nil => simp [valueDigits]
  | cons bit later ih =>
    cases bit <;> simp [valueDigits, Nat.bit, Nat.pow_succ] <;> omega

theorem last_true_nonzero (digits : List Bool) (h : digits.getLast? = some true) :
    valueDigits digits ≠ 0 := by
  have hne : digits ≠ [] := by intro hh; simp [hh] at h
  have hlen : 0 < digits.length := List.length_pos_iff.mpr hne
  have hb : (valueDigits digits).testBit (digits.length - 1) = true := by
    rw [testBit_valueDigits, List.getI_eq_getElem _ (by omega)]
    have hh := h
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some.inj hh
  intro hz
  simp [hz] at hb

theorem canonical_width (digits : List Bool) (h : digits.getLast? = some true) :
    natBits (valueDigits digits) = digits.length := by
  have hn := last_true_nonzero digits h
  have hne : digits ≠ [] := by intro hh; simp [hh] at h
  have hlen : 0 < digits.length := List.length_pos_iff.mpr hne
  have hb : (valueDigits digits).testBit (digits.length - 1) = true := by
    rw [testBit_valueDigits, List.getI_eq_getElem _ (by omega)]
    have hh := h
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some.inj hh
  have hlo : 2 ^ (digits.length - 1) ≤ valueDigits digits := by
    by_contra hh
    have hf := Nat.testBit_eq_false_of_lt (Nat.lt_of_not_ge hh)
    rw [hb] at hf
    cases hf
  have hlog : (valueDigits digits).log2 = digits.length - 1 := by
    apply (Nat.log2_eq_iff hn).mpr
    refine ⟨hlo, ?_⟩
    simpa only [Nat.sub_add_cancel hlen] using valueDigits_lt digits
  simp only [natBits, hlog]
  omega

theorem canonical_digits (digits : List Bool) (h : digits.getLast? = some true) :
    digits = rawPayload (valueDigits digits) := by
  apply List.ext_getElem
  · simpa only [rawPayload, List.length_ofFn] using (canonical_width digits h).symm
  · intro i hi hj
    have he := testBit_valueDigits digits i
    rw [List.getI_eq_getElem _ hi] at he
    simpa only [rawPayload, List.getElem_ofFn] using he.symm

theorem bump_last_true (digits : List Bool) (h : digits.getLast? = some true) :
    (bumpDigits digits).getLast? = some true := by
  induction digits with
  | nil => simp at h
  | cons bit later ih =>
    cases later with
    | nil => cases bit <;> rfl
    | cons next rest =>
      have ht : (next :: rest).getLast? = some true := by simpa using h
      cases bit with
      | false => simpa [bumpDigits] using ht
      | true =>
        rw [bumpDigits, List.getLast?_cons_of_ne_nil (bump_ne_nil (next :: rest))]
        exact ih ht

theorem rawPayload_last (value : Nat) (hn : value ≠ 0) :
    (rawPayload value).getLast? = some true := by
  rw [List.getLast?_eq_getElem?]
  simp only [rawPayload, List.length_ofFn, natBits, Nat.add_sub_cancel_right]
  rw [List.getElem?_eq_getElem (by simp)]
  simpa only [List.getElem_ofFn] using congrArg some (Nat.testBit_log2 hn)

theorem bump_rawPayload_last (value : Nat) :
    (bumpDigits (rawPayload value)).getLast? = some true := by
  by_cases hn : value = 0
  · subst value
    rfl
  · exact bump_last_true _ (rawPayload_last value hn)

theorem bump_rawPayload_eq (value : Nat) :
    bumpDigits (rawPayload value) = rawPayload (value + 1) := by
  have hc := canonical_digits _ (bump_rawPayload_last value)
  rw [valueDigits_bumpDigits, valueDigits_rawPayload] at hc
  exact hc

theorem rawWord_bump (value : Nat) :
    PSTRTMUnblockTrace019.rawWord (bumpDigits (rawPayload value)) = encodeNat (value + 1) := by
  rw [bump_rawPayload_eq]
  simp [PSTRTMUnblockTrace019.rawWord, rawPayload, encodeNat]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCanonical020
