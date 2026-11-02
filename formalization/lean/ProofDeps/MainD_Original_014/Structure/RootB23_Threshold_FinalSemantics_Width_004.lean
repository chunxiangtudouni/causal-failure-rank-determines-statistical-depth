module
public import Structure.RootB23_Threshold_FinalSemantics_Identity_001
public import Structure.RootB23_Threshold_FinalSerialize_Schema_001
public import Structure.PA17_TM_RatArithmetic_MulFields_048b

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.FinalSemantics
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Statistics
open PA17TMRatArithmeticParse002

def inputScale (risk : Rat) (depth : Nat) : Nat :=
  (encode [.rational risk,.natural depth]).length+depth+1

private theorem width_bits (b : Nat) (t r o i : Rat) : FinalSerialize.totalWidth b t r o i =
    natBits b+natBits t.num.natAbs+natBits t.den+natBits r.num.natAbs+natBits r.den+
      natBits o.num.natAbs+natBits o.den+natBits i.num.natAbs+natBits i.den := by
  simp only [FinalSerialize.totalWidth,FinalSerialize.nineFields,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    numeratorDigits_length,denominatorDigits_length,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  omega

/-- Canonical product field bounds are reused without a restriction
risk<=1/4. Capping selects a real Rat value; it cannot enlarge these
semantic field widths beyond the fixed quarter alternative. -/
theorem badRisk_width_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    natBits (controllerBadRisk risk (controllerTarget risk depth)).num.natAbs+
      natBits (controllerBadRisk risk (controllerTarget risk depth)).den ≤
      4*(encode [.rational risk,.natural depth]).length+20 := by
  let input := (encode [.rational risk,.natural depth]).length
  have factor : natBits (FactorSource.factorValue risk depth) ≤ input+6 := by
    simpa only [FactorSource.factorValue,input] using PSTRTMThresholdBadFactor226.factor_bits_le risk depth hr hd
  have original := PSTRTMThresholdRisk114.original_widths_le risk depth hr
  change natBits risk.num.natAbs+natBits risk.den ≤ input+1 at original
  have unit : natBits 1=1 := by decide
  have fields : fieldWidth (FactorSource.factorValue risk depth : Rat) risk ≤ 2*input+8 := by
    simp only [fieldWidth,numeratorDigits_length,denominatorDigits_length,Rat.num_natCast,
      Int.natAbs_natCast,Rat.den_natCast,unit]
    omega
  have normalized := PA17TMRatArithmeticMulFields048.normalized_bits (FactorSource.factorValue risk depth : Rat) risk
  have values := PA17TMRatArithmeticMulFields048.pipeline_fields (FactorSource.factorValue risk depth : Rat) risk
  rw [values.1,values.2.1] at normalized
  have product : natBits ((FactorSource.factorValue risk depth : Rat)*risk).num.natAbs+
      natBits ((FactorSource.factorValue risk depth : Rat)*risk).den ≤ 4*input+16 := by omega
  have quarter : natBits (1/4 : Rat).num.natAbs+natBits (1/4 : Rat).den=4 := by
    have numerator : (1/4 : Rat).num=1 := by
      rw [one_div]
      exact Rat.inv_natCast_num_of_pos (by decide : 0 < (4 : Nat))
    have denominator : (1/4 : Rat).den=4 := by
      rw [one_div]
      exact Rat.inv_natCast_den_of_pos (by decide : 0 < (4 : Nat))
    rw [numerator,denominator,Int.natAbs_one]
    decide
  rw [← badRisk_identity]
  by_cases capped : (1/4 : Rat) ≤ (FactorSource.factorValue risk depth : Rat)*risk
  · rw [min_eq_left capped,quarter]
    omega
  · rw [min_eq_right (le_of_not_ge capped)]
    omega

/-- The exact final nine-digit SUM, with fixed coefficient before ALL
original inputs. No width, room, source bank or copy trace is supplied by
the original caller. -/
theorem nine_width_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    FinalSerialize.totalWidth (controllerB risk depth) (controllerTarget risk depth)
      (controllerBadRisk risk (controllerTarget risk depth))
      ((1-controllerTarget risk depth)/controllerTarget risk depth)
      (controllerTarget risk depth/(1-controllerTarget risk depth))+1 ≤128*inputScale risk depth := by
  let input := (encode [.rational risk,.natural depth]).length
  have bWidth := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  change natBits (controllerB risk depth) ≤ input+4 at bWidth
  have denominatorWidth := OutputArithmetic.Target.denominator_width (controllerB risk depth)
  change natBits (4*(controllerB risk depth+1)) ≤ natBits (controllerB risk depth)+3 at denominatorWidth
  have oddsWidth := PSTRTMArithmetic008.natBits_mono (Nat.sub_le (4*(controllerB risk depth+1)) 1)
  have badWidth := badRisk_width_le risk depth hr hd
  have positive := PSTRTMThresholdOddsFields211.oddsValue_pos risk depth
  have unit : natBits 1=1 := by decide
  rw [width_bits,PSTRTMThresholdDenominatorRaw202.target_numerator,
    PSTRTMThresholdDenominatorRaw202.target_denominator,PSTRTMThresholdOddsFields211.controller_odds_identity,
    PSTRTMThresholdOddsFields211.controller_inverse_odds_identity,one_div]
  simp only [Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast,Rat.inv_natCast_num_of_pos positive,
    Rat.inv_natCast_den_of_pos positive,Int.natAbs_one,unit]
  dsimp only [PSTRTMThresholdOddsFields211.oddsValue,inputScale] at *
  omega

/-- Same bound with the exact physical producer values. The old semantic
identities are only rewrites, not independent output tapes. -/
theorem actual_payload_width_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    FinalSerialize.totalWidth (controllerB risk depth) (OutputArithmetic.Target.value (controllerB risk depth))
      (min (1/4) ((FactorSource.factorValue risk depth : Rat)*risk))
      (((OutputArithmetic.Target.denominator (controllerB risk depth)-1 : Nat) : Rat))
      (1/((OutputArithmetic.Target.denominator (controllerB risk depth)-1 : Nat) : Rat))+1 ≤
      128*inputScale risk depth := by
  have target : OutputArithmetic.Target.value (controllerB risk depth)=controllerTarget risk depth :=
    (PSTRTMThresholdDenominatorRaw202.target_denominator_identity risk depth).symm
  have odds : ((OutputArithmetic.Target.denominator (controllerB risk depth)-1 : Nat) : Rat)=
      (1-controllerTarget risk depth)/controllerTarget risk depth :=
    (PSTRTMThresholdOddsFields211.controller_odds_identity risk depth).symm
  have inverse : 1/((OutputArithmetic.Target.denominator (controllerB risk depth)-1 : Nat) : Rat)=
      controllerTarget risk depth/(1-controllerTarget risk depth) :=
    (PSTRTMThresholdOddsFields211.controller_inverse_odds_identity risk depth).symm
  rw [target,badRisk_identity,inverse,odds]
  exact nine_width_le risk depth hr hd

end RootB23.Threshold.FinalSemantics
