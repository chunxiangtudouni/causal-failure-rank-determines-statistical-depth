module
public import Structure.PA17_TM_RatArithmetic_Size_007c

/-! Canonical gcd quotients do not increase the true field bit lengths.
The denominator-zero branch is included: both zero and one use one bit. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeSize007
open PA17TMRatArithmeticSemantics001 PSTRTMArithmetic008 PSTRTMLength004

theorem canonicalMagnitude_le (magnitude denominator : Nat) :
    canonicalMagnitude magnitude denominator ≤ magnitude := by
  by_cases hd : denominator = 0
  · simp [canonicalMagnitude,hd]
  · simpa only [canonicalMagnitude,ite_eq_right hd] using
      Nat.div_le_self magnitude (Nat.gcd magnitude denominator)

theorem canonicalMagnitude_bits_le (magnitude denominator : Nat) :
    natBits (canonicalMagnitude magnitude denominator) ≤ natBits magnitude :=
  natBits_mono (canonicalMagnitude_le magnitude denominator)

theorem canonicalDenominator_bits_le (magnitude denominator : Nat) :
    natBits (canonicalDenominator magnitude denominator) ≤ natBits denominator := by
  by_cases hd : denominator = 0
  · simp [canonicalDenominator,hd,natBits]
  · apply natBits_mono
    simpa only [canonicalDenominator,ite_eq_right hd] using
      Nat.div_le_self denominator (Nat.gcd magnitude denominator)

theorem normalized_candidate_bits_le (negative : Bool) (magnitude denominator : Nat) (q : Rat)
    (value : mkRat (signed negative magnitude) denominator = q) :
    natBits q.num.natAbs ≤ natBits magnitude ∧ natBits q.den ≤ natBits denominator := by
  obtain ⟨hm,hd,_⟩ := signed_candidate_fields negative magnitude denominator q value
  rw [hm,hd]
  exact ⟨canonicalMagnitude_bits_le magnitude denominator,canonicalDenominator_bits_le magnitude denominator⟩

theorem add_normalized_bits_le (x y : Rat) :
    natBits (x+y).num.natAbs ≤ inputBits x y ∧ natBits (x+y).den ≤ inputBits x y := by
  obtain ⟨hm,hd⟩ := normalized_candidate_bits_le _ _ _ _ (add_signed_value x y)
  exact ⟨hm.trans (addMagnitude_bits_le x y),hd.trans (productDen_bits_le x y)⟩

theorem sub_normalized_bits_le (x y : Rat) :
    natBits (x-y).num.natAbs ≤ inputBits x y ∧ natBits (x-y).den ≤ inputBits x y := by
  obtain ⟨hm,hd⟩ := normalized_candidate_bits_le _ _ _ _ (sub_signed_value x y)
  exact ⟨hm.trans (subMagnitude_bits_le x y),hd.trans (productDen_bits_le x y)⟩

theorem mul_normalized_bits_le (x y : Rat) :
    natBits (x*y).num.natAbs ≤ inputBits x y ∧ natBits (x*y).den ≤ inputBits x y := by
  obtain ⟨hm,hd⟩ := normalized_candidate_bits_le _ _ _ _ (mul_signed_value x y)
  exact ⟨hm.trans (mulMagnitude_bits_le x y),hd.trans (productDen_bits_le x y)⟩

theorem div_normalized_bits_le (x y : Rat) :
    natBits (x/y).num.natAbs ≤ inputBits x y ∧ natBits (x/y).den ≤ inputBits x y := by
  obtain ⟨hm,hd⟩ := normalized_candidate_bits_le _ _ _ _ (div_signed_value x y)
  exact ⟨hm.trans (divMagnitude_bits_le x y),hd.trans (quotientDen_bits_le x y)⟩

theorem singleton_output_length (q : Rat) :
    (encode [.rational q]).length = 2 * (natBits q.num.natAbs + natBits q.den) + 8 := by
  rw [encode_length]
  simp only [List.length_singleton,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,datumBits]
  have ho : natBits 1 = 1 := rfl
  rw [ho]
  omega

theorem output_length_le_twice_input (x y q : Rat)
    (hm : natBits q.num.natAbs ≤ inputBits x y) (hd : natBits q.den ≤ inputBits x y) :
    (encode [.rational q]).length ≤ 2 * (encode [.rational x,.rational y]).length := by
  rw [singleton_output_length,input_length]
  omega

theorem add_output_length_le (x y : Rat) :
    (encode [.rational (x+y)]).length ≤ 2 * (encode [.rational x,.rational y]).length := by
  obtain ⟨hm,hd⟩ := add_normalized_bits_le x y
  exact output_length_le_twice_input x y (x+y) hm hd

theorem sub_output_length_le (x y : Rat) :
    (encode [.rational (x-y)]).length ≤ 2 * (encode [.rational x,.rational y]).length := by
  obtain ⟨hm,hd⟩ := sub_normalized_bits_le x y
  exact output_length_le_twice_input x y (x-y) hm hd

theorem mul_output_length_le (x y : Rat) :
    (encode [.rational (x*y)]).length ≤ 2 * (encode [.rational x,.rational y]).length := by
  obtain ⟨hm,hd⟩ := mul_normalized_bits_le x y
  exact output_length_le_twice_input x y (x*y) hm hd

theorem div_output_length_le (x y : Rat) :
    (encode [.rational (x/y)]).length ≤ 2 * (encode [.rational x,.rational y]).length := by
  obtain ⟨hm,hd⟩ := div_normalized_bits_le x y
  exact output_length_le_twice_input x y (x/y) hm hd

theorem four_operations_original_input_bounds (x y : Rat) :
    (encode [.rational (x+y)]).length ≤ 2 * (encode [.rational x,.rational y]).length ∧
    (encode [.rational (x-y)]).length ≤ 2 * (encode [.rational x,.rational y]).length ∧
    (encode [.rational (x*y)]).length ≤ 2 * (encode [.rational x,.rational y]).length ∧
    (encode [.rational (x/y)]).length ≤ 2 * (encode [.rational x,.rational y]).length :=
  ⟨add_output_length_le x y,sub_output_length_le x y,mul_output_length_le x y,div_output_length_le x y⟩

theorem encodeNat_field_length_le (value width : Nat) (h : natBits value ≤ width) :
    (encodeNat value).length ≤ 2*width+1 := by
  rw [encodeNat_length]
  omega

theorem candidate_gcd_input_length_le (x y : Rat) (magnitude denominator : Nat)
    (hm : natBits magnitude ≤ inputBits x y) (hd : natBits denominator ≤ inputBits x y) :
    (encodeNat magnitude ++ encodeNat denominator).length ≤
      2 * (encode [.rational x,.rational y]).length := by
  rw [List.length_append,encodeNat_length,encodeNat_length,input_length]
  omega

/-- Scaling the actual frozen native-gcd constants to original Rat input
length. This is only arithmetic on budgets; Runs is supplied by the real gcd. -/
theorem candidate_gcd_budget_le (x y : Rat) (magnitude denominator : Nat)
    (hm : natBits magnitude ≤ inputBits x y) (hd : natBits denominator ≤ inputBits x y) :
    16384*(natBits magnitude+natBits denominator+1)^2 ≤
      65536*((encode [.rational x,.rational y]).length+1)^2 ∧
    65536*(natBits magnitude+natBits denominator+1)^2 ≤
      262144*((encode [.rational x,.rational y]).length+1)^2 := by
  have hi := inputBits_le_input_length x y
  have hwidth : natBits magnitude+natBits denominator+1 ≤
      2*((encode [.rational x,.rational y]).length+1) := by omega
  have hp := Nat.pow_le_pow_left hwidth 2
  rw [Nat.mul_pow] at hp
  change (natBits magnitude+natBits denominator+1)^2 ≤
    4*((encode [.rational x,.rational y]).length+1)^2 at hp
  constructor <;> omega

theorem normalized_fields_bits_le_input (x y : Rat) :
    natBits (x+y).num.natAbs ≤ (encode [.rational x,.rational y]).length ∧
    natBits (x+y).den ≤ (encode [.rational x,.rational y]).length ∧
    natBits (x-y).num.natAbs ≤ (encode [.rational x,.rational y]).length ∧
    natBits (x-y).den ≤ (encode [.rational x,.rational y]).length ∧
    natBits (x*y).num.natAbs ≤ (encode [.rational x,.rational y]).length ∧
    natBits (x*y).den ≤ (encode [.rational x,.rational y]).length ∧
    natBits (x/y).num.natAbs ≤ (encode [.rational x,.rational y]).length ∧
    natBits (x/y).den ≤ (encode [.rational x,.rational y]).length := by
  have hi := inputBits_le_input_length x y
  obtain ⟨ha,hb⟩ := add_normalized_bits_le x y
  obtain ⟨hc,hd⟩ := sub_normalized_bits_le x y
  obtain ⟨he,hf⟩ := mul_normalized_bits_le x y
  obtain ⟨hg,hh⟩ := div_normalized_bits_le x y
  exact ⟨ha.trans hi,hb.trans hi,hc.trans hi,hd.trans hi,
    he.trans hi,hf.trans hi,hg.trans hi,hh.trans hi⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeSize007
