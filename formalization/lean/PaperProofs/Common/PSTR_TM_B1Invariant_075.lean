module
public import PaperProofs.Common.PSTR_TM_B1Iteration_074
public import PaperProofs.Common.PSTR_TM_B1Value_068

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1Invariant075
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMBinaryAdd024 PSTRTMShiftColumnCode065 PSTRTMNatValue017

def initialPairs (numerator denominator : Nat) : List (Bool × Bool) :=
  PSTRTMB1PrepareCode069.paddedPairs (PSTRTMPackCode036.digitPairs (rawPayload numerator) (rawPayload denominator))

def iteratedPairs (pairs : List (Bool × Bool)) : Nat → List (Bool × Bool)
  | 0 => pairs
  | count + 1 => shiftPairs false (iteratedPairs pairs count)

theorem padded_values (pairs : List (Bool × Bool)) :
    firstValue (PSTRTMB1PrepareCode069.paddedPairs pairs) = firstValue pairs ∧
    secondValue (PSTRTMB1PrepareCode069.paddedPairs pairs) = secondValue pairs := by
  induction pairs with
  | nil => exact ⟨rfl,rfl⟩
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    change Nat.bit a (firstValue (PSTRTMB1PrepareCode069.paddedPairs later)) = Nat.bit a (firstValue later) ∧
      Nat.bit b (secondValue (PSTRTMB1PrepareCode069.paddedPairs later)) = Nat.bit b (secondValue later)
    rw [ih.1,ih.2]
    exact ⟨rfl,rfl⟩

theorem initial_values (numerator denominator : Nat) :
    firstValue (initialPairs numerator denominator) = numerator ∧
      secondValue (initialPairs numerator denominator) = denominator := by
  have hp := padded_values (PSTRTMPackCode036.digitPairs (rawPayload numerator) (rawPayload denominator))
  have hv := PSTRTMAddCanonical052.digitPairs_values (rawPayload numerator) (rawPayload denominator)
  constructor
  · change firstValue (PSTRTMB1PrepareCode069.paddedPairs _) = numerator
    rw [hp.1,hv.1,valueDigits_rawPayload]
  · change secondValue (PSTRTMB1PrepareCode069.paddedPairs _) = denominator
    rw [hp.2,hv.2,valueDigits_rawPayload]

theorem initial_length (numerator denominator : Nat) :
    (initialPairs numerator denominator).length = max (natBits numerator) (natBits denominator) + 1 := by
  simp only [initialPairs, PSTRTMB1PrepareCode069.paddedPairs, List.length_append, List.length_cons, List.length_nil,
    PSTRTMPackCode036.digitPairs_length, rawPayload, List.length_ofFn]

theorem iterated_length (pairs : List (Bool × Bool)) (count : Nat) :
    (iteratedPairs pairs count).length = pairs.length := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [iteratedPairs, shiftPairs_length, ih]

theorem iterated_second (numerator denominator count : Nat) :
    secondValue (iteratedPairs (initialPairs numerator denominator) count) = denominator := by
  induction count with
  | zero => exact (initial_values numerator denominator).2
  | succ count ih => simpa only [iteratedPairs, secondValue_shiftPairs] using ih

theorem noOverflow_of_double_lt (pairs : List (Bool × Bool)) (hcapacity : 2*firstValue pairs < 2^pairs.length) :
    finalCarry false pairs = false := by
  have hv := firstValue_shiftPairs false pairs
  cases hc : finalCarry false pairs with
  | false => rfl
  | true =>
    rw [hc] at hv
    simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.add_zero] at hv
    omega

theorem shifted_value_noOverflow (pairs : List (Bool × Bool)) (hc : finalCarry false pairs = false) :
    firstValue (shiftPairs false pairs) = 2*firstValue pairs := by
  simpa only [hc, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] using firstValue_shiftPairs false pairs

theorem iterated_first (numerator denominator count : Nat) (hn : 0 < numerator)
    (hcount : count ≤ PSTRTMB1Value068.exponent numerator denominator) :
    firstValue (iteratedPairs (initialPairs numerator denominator) count) = numerator*2^count := by
  induction count with
  | zero => simpa only [iteratedPairs, Nat.pow_zero, Nat.mul_one] using (initial_values numerator denominator).1
  | succ count ih =>
    have hlt : count < PSTRTMB1Value068.exponent numerator denominator := by omega
    have hcur := ih (by omega)
    have hcapacity : 2*firstValue (iteratedPairs (initialPairs numerator denominator) count) <
        2^(iteratedPairs (initialPairs numerator denominator) count).length := by
      rw [hcur,iterated_length,initial_length]
      exact PSTRTMB1Value068.doubled_strict_before_capacity numerator denominator count hn hlt
    have hc := noOverflow_of_double_lt _ hcapacity
    rw [iteratedPairs,shifted_value_noOverflow _ hc,hcur,Nat.pow_succ]
    ring

/-- Derived from ORIGINAL input values and the physically allocated070
extra column. noOverflow is NOT an added original input assumption. -/
theorem actual_noOverflow_before (numerator denominator count : Nat) (hn : 0 < numerator)
    (hcount : count < PSTRTMB1Value068.exponent numerator denominator) :
    finalCarry false (iteratedPairs (initialPairs numerator denominator) count) = false := by
  apply noOverflow_of_double_lt
  rw [iterated_first numerator denominator count hn (by omega), iterated_length, initial_length]
  exact PSTRTMB1Value068.doubled_strict_before_capacity numerator denominator count hn hcount

theorem comparison_less_before (numerator denominator count : Nat) (hn : 0 < numerator)
    (hcount : count < PSTRTMB1Value068.exponent numerator denominator) :
    PSTRTMCompareCode054.resultRelation 0 (iteratedPairs (initialPairs numerator denominator) count) = 1 := by
  rw [PSTRTMCompareValue056.resultRelation_classify, iterated_first numerator denominator count hn (by omega), iterated_second]
  have hs := PSTRTMB1Value068.exponent_strict_before numerator denominator count hn hcount
  simp [PSTRTMCompareValue056.classify, show numerator*2^count ≠ denominator by omega, hs]

theorem comparison_not_less_final (numerator denominator : Nat) (hn : 0 < numerator) :
    PSTRTMCompareCode054.resultRelation 0
      (iteratedPairs (initialPairs numerator denominator) (PSTRTMB1Value068.exponent numerator denominator)) ≠ 1 := by
  rw [PSTRTMCompareValue056.resultRelation_classify, iterated_first numerator denominator _ hn le_rfl, iterated_second]
  have hs := PSTRTMB1Value068.exponent_stop numerator denominator hn
  by_cases he : numerator*2^PSTRTMB1Value068.exponent numerator denominator = denominator
  · simp [PSTRTMCompareValue056.classify, he]
  · have hnlt : ¬numerator*2^PSTRTMB1Value068.exponent numerator denominator < denominator := by omega
    simp [PSTRTMCompareValue056.classify, he, hnlt]

theorem nextDigits_rawPayload (count : Nat) :
    PSTRTMB1Iteration074.nextDigits (rawPayload count) = rawPayload (count+1) :=
  PSTRTMCanonical020.bump_rawPayload_eq count

/-- The real counter bit length is at most ORIGINAL denominator bit length.
Neither counter value nor an output maximum is substituted as a new input. -/
theorem counter_payload_length_le (numerator denominator count : Nat) (hn : 0 < numerator)
    (hcount : count ≤ PSTRTMB1Value068.exponent numerator denominator) :
    (rawPayload count).length ≤ natBits denominator := by
  have hc := PSTRTMArithmetic008.natBits_mono (hcount.trans (PSTRTMB1Value068.exponent_le_bits numerator denominator hn))
  have hp : 0 < natBits denominator := by simp [natBits]
  have hb := PSTRTMArithmetic008.natBits_le_of_lt_pow (natBits denominator) (natBits denominator)
    Nat.lt_two_pow_self hp
  simp only [rawPayload, List.length_ofFn]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1Invariant075
