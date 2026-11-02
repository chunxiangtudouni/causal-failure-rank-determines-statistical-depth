module
public import Common.PSTR_TM_ThresholdCapCaller_236
public import Common.PSTR_TM_ThresholdBadFactor_226

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdProductBits237
open PaperProofs.Common.Native.RationalControllerComputation

/-! Width of the actual positive integer multiple used by badRisk.
This is a semantic width bridge for the RawMul result and its REAL future
cap-call packet. It neither performs multiplication nor supplies a width,
result or room certificate in the original input. -/

private theorem natBits_mul_le (a b : Nat) : natBits (a*b) ≤ natBits a+natBits b := by
  have ha := PSTRTMCodec001.natBits_bound a
  have hb := PSTRTMCodec001.natBits_bound b
  have hle := Nat.mul_le_mul_left a hb.le
  have hlt := Nat.mul_lt_mul_of_pos_right ha (by positivity : 0 < 2^natBits b)
  apply PSTRTMArithmetic008.natBits_le_of_lt_pow
  · rw [Nat.pow_add]
    exact lt_of_le_of_lt hle hlt
  · have hp : 0 < natBits a := by simp [natBits]
    omega

def product (risk : Rat) (depth : Nat) : Rat :=
  risk*(PSTRTMThresholdBadFactor226.factor risk depth : Rat)

theorem product_den_le (risk : Rat) (depth : Nat) :
    (product risk depth).den ≤ risk.den :=
  PSTRTMReferenceRiskBits225.den_mul_nat_le _ _

theorem product_num_abs_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hq : risk ≤ 1/4) :
    (product risk depth).num.natAbs ≤ PSTRTMThresholdBadFactor226.factor risk depth*risk.den := by
  have hf : 0 < (PSTRTMThresholdBadFactor226.factor risk depth : Rat) := by
    dsimp only [PSTRTMThresholdBadFactor226.factor]
    positivity
  have hp : 0 < product risk depth := mul_pos hr hf
  have hrone : risk ≤ 1 := hq.trans (by norm_num)
  have hprod : product risk depth ≤ (PSTRTMThresholdBadFactor226.factor risk depth : Rat) := by
    exact (mul_le_mul_of_nonneg_right hrone hf.le).trans_eq (one_mul _)
  have hn := (Rat.le_iff (product risk depth) (PSTRTMThresholdBadFactor226.factor risk depth : Rat)).mp hprod
  simp only [Rat.den_natCast,Rat.num_natCast,Int.ofNat_one,Int.mul_one] at hn
  have habs : ((product risk depth).num.natAbs : Int) ≤
      (PSTRTMThresholdBadFactor226.factor risk depth : Int)*(product risk depth).den := by
    rw [Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hp.le)]
    exact hn
  have hnat : (product risk depth).num.natAbs ≤
      PSTRTMThresholdBadFactor226.factor risk depth*(product risk depth).den := by exact_mod_cast habs
  exact hnat.trans (Nat.mul_le_mul_left _ (product_den_le risk depth))

theorem product_bits_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hq : risk ≤ 1/4) (hd : 1 ≤ depth) :
    natBits (product risk depth).num.natAbs+natBits (product risk depth).den ≤
      3*(encode [.rational risk,.natural depth]).length+8 := by
  have hn := (PSTRTMArithmetic008.natBits_mono (product_num_abs_le risk depth hr hq)).trans
    (natBits_mul_le (PSTRTMThresholdBadFactor226.factor risk depth) risk.den)
  have hden := PSTRTMArithmetic008.natBits_mono (product_den_le risk depth)
  have hf := PSTRTMThresholdBadFactor226.factor_bits_le risk depth hr hd
  have hin := PSTRTMThresholdRisk114.original_widths_le risk depth hr
  omega

/-- The actual future original[q,1] cap packet has LINEAR bit length
in the original[risk,depth] packet, even if q exceeds the cap. Original
risk qualifications suffice; q is not required to lie below1/4. -/
theorem cap_packet_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hq : risk ≤ 1/4) (hd : 1 ≤ depth) :
    (encode [.rational (product risk depth),.natural 1]).length ≤
      6*(encode [.rational risk,.natural depth]).length+30 := by
  have hb := product_bits_le risk depth hr hq hd
  have h1 : natBits 1 = 1 := by decide
  have h2 : natBits 2 = 2 := by decide
  conv_lhs => simp only [PSTRTMLength004.encode_length,List.length_cons,List.length_nil,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,PSTRTMLength004.datumBits,h1,h2]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdProductBits237
