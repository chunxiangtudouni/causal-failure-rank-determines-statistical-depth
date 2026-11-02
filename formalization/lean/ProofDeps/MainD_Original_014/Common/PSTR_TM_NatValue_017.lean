module
public import Common.PSTR_TM_ProtectedIncrement_016
public import Common.PSTR_TM_Codec_001

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNatValue017
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009 PSTRTMIncrementFrame013 PSTRTMProtectedIncrement016

theorem testBit_valueDigits (digits : List Bool) (index : Nat) :
    (valueDigits digits).testBit index = digits.getI index := by
  induction digits generalizing index with
  | nil => simp [valueDigits]
  | cons bit later ih =>
    cases index with
    | zero => simp [valueDigits]
    | succ index => simpa only [valueDigits, Nat.testBit_bit_succ, List.getI_cons_succ] using ih index

def rawPayload (value : Nat) : List Bool :=
  List.ofFn (fun i : Fin (natBits value) => value.testBit i.val)

/-- The actual original raw payload denotes its claimed integer, including0. -/
theorem valueDigits_rawPayload (value : Nat) : valueDigits (rawPayload value) = value := by
  apply Nat.eq_of_testBit_eq
  intro index
  rw [testBit_valueDigits]
  by_cases hi : index < natBits value
  · rw [List.getI_eq_getElem _ (by simpa [rawPayload] using hi)]
    simp [rawPayload]
  · rw [List.getI_eq_default _ (by simpa [rawPayload] using Nat.le_of_not_gt hi)]
    symm
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le (PSTRTMCodec001.natBits_bound value)
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi))

/-- End-to-end numeric correctness of the fixed122-label raw-input program.
The witness is its real finite Runs/transition trace with original cost
measures. The output format remains the exposed internal flagged cells. -/
theorem raw_increment_exact (value : Nat) (suffix : List Bool) :
    computes protectedIncrementMachine (encodeNat value ++ suffix)
      (blocks (bumpDigits (rawPayload value)) ++ remainingPad (rawPayload value) ++ true :: false :: suffix)
      (1024 * (natBits value + 1) ^ 2) (1024 * (natBits value + 1) ^ 2 + suffix.length) ∧
      valueDigits (bumpDigits (rawPayload value)) = value + 1 := by
  constructor
  · exact encodeNat_protected_increment_computes value suffix
  · rw [valueDigits_bumpDigits, valueDigits_rawPayload]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNatValue017
