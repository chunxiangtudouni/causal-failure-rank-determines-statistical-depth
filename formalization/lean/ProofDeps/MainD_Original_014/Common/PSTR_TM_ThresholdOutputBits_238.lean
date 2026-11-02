module
public import Common.PSTR_TM_ThresholdProductBits_237
public import Common.PSTR_TM_ThresholdOddsFields_211

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdOutputBits238
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Statistics PSTRTMLength004 PSTRTMThresholdOddsFields211

/-! Bit width of the ORIGINAL complete five-Datum output, using canonical
Rat fields. This does not serialize those five fields or supply them as an
input. Real producers, q preservation, calls and final list assembly remain
necessary. The bound is independent of numerical depth, even though its
real B computation is charged using the original input.length+depth budget. -/

theorem thresholdOutput_length_le (risk : Rat) (depth : Nat)
    (hr : 0 < risk) (hq : risk ≤ 1/4) (hd : 1 ≤ depth) :
    (thresholdOutput risk depth).length ≤ 12*(encode [.rational risk,.natural depth]).length+86 := by
  have hB := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  have hD := PSTRTMThresholdDenominatorCost201.targetDen_bits_le risk depth hr hd
  have hO : natBits (oddsValue risk depth) ≤ (encode [.rational risk,.natural depth]).length+7 :=
    (PSTRTMArithmetic008.natBits_mono (Nat.sub_le _ 1)).trans hD
  have hinput := PSTRTMThresholdRisk114.original_widths_le risk depth hr
  have h1 : natBits 1 = 1 := by decide
  have hBdatum : datumBits (.natural (controllerB risk depth)) ≤
      2*(encode [.rational risk,.natural depth]).length+10 := by
    change 2*natBits (controllerB risk depth)+2 ≤ _
    omega
  have htarget : datumBits (.rational (controllerTarget risk depth)) ≤
      2*(encode [.rational risk,.natural depth]).length+20 := by
    rw [←encodeDatum_length,PSTRTMThresholdDenominatorRaw202.target_datum_bits]
    simp only [List.length_append,List.length_cons,List.length_nil,encodeNat_length,h1]
    omega
  have hupper : datumBits (.rational ((1-controllerTarget risk depth)/controllerTarget risk depth)) ≤
      2*(encode [.rational risk,.natural depth]).length+20 := by
    rw [←encodeDatum_length,odds_datum_bits]
    simp only [List.length_append,List.length_cons,List.length_nil,encodeNat_length,h1]
    omega
  have hinverse : datumBits (.rational (controllerTarget risk depth/(1-controllerTarget risk depth))) ≤
      2*(encode [.rational risk,.natural depth]).length+20 := by
    rw [←encodeDatum_length,inverse_odds_datum_bits]
    simp only [List.length_append,List.length_cons,List.length_nil,encodeNat_length,h1]
    omega
  have hstep : referenceBudgetStep (.finiteBad ⟨depth,by omega⟩) true risk =
      some (controllerBadRisk risk (controllerTarget risk depth)) := rfl
  have hvalid := (referenceBudgetStep_valid_floor (.finiteBad ⟨depth,by omega⟩) true risk
    (controllerBadRisk risk (controllerTarget risk depth)) ⟨hr,hq⟩ hstep).1
  have hbadDen := PSTRTMReferenceRiskBits225.badRisk_den_le risk depth hr hq
  have hbadNum := PSTRTMReferenceRiskBits225.valid_num_abs_le_den
    (controllerBadRisk risk (controllerTarget risk depth)) hvalid
  have hbadDenBits := PSTRTMArithmetic008.natBits_mono hbadDen
  have hbadNumBits := (PSTRTMArithmetic008.natBits_mono hbadNum).trans hbadDenBits
  have hbad : datumBits (.rational (controllerBadRisk risk (controllerTarget risk depth))) ≤
      4*(encode [.rational risk,.natural depth]).length+8 := by
    change 2*(natBits (controllerBadRisk risk (controllerTarget risk depth)).num.natAbs+
      natBits (controllerBadRisk risk (controllerTarget risk depth)).den)+4 ≤ _
    omega
  have hlen : (thresholdOutput risk depth).length =
      8+datumBits (.natural (controllerB risk depth))+
        datumBits (.rational (controllerTarget risk depth))+
        datumBits (.rational (controllerBadRisk risk (controllerTarget risk depth)))+
        datumBits (.rational ((1-controllerTarget risk depth)/controllerTarget risk depth))+
        datumBits (.rational (controllerTarget risk depth/(1-controllerTarget risk depth))) := by
    rw [thresholdOutput,encode_length]
    have h5 : natBits 5 = 3 := by decide
    simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,h5]
    omega
  rw [hlen]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdOutputBits238
