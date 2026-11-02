module
public import Common.PSTR_TM_ThresholdRiskMarkers_232

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRiskSource233
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdRiskLocator231 PSTRTMThresholdRiskMarkers232

/-! Fixed1365-label ORIGINAL input caller. After producing2*(B+1), the
same machine physically crosses saved B, cleared gap, exhausted DEPTH,
and both ORIGINAL risk markers back to the NUM first digit. The entire
DEN/DEPTH/gap/B/factor suffix survives. This is a source locator for
actual arithmetic/serialization, not badRisk or the five-Datum result. -/

def riskSourceMachine : Machine 1364 := PSTRTMSeq005.seqMachine locatorMachine riskFieldsMachine

def numerator (risk : Rat) : List Bool := PSTRTMNatValue017.rawPayload risk.num.natAbs
def denominator (risk : Rat) : List Bool := PSTRTMNatValue017.rawPayload risk.den

def sourceRight (risk : Rat) (depth : Nat) : List Bool :=
  PSTRTMIncrement009.blocks (numerator risk)++
    markerTail (PSTRTMIncrement009.blocks (denominator risk)++markerTail (locatorRight risk depth))

theorem original_marker_entry (risk : Rat) :
    false::PSTRTMThresholdDepthSource184.riskArchive risk =
      markerLeft (PSTRTMThresholdDenPrepare141.denArchive [] (numerator risk)) (denominator risk) := rfl

theorem sourceRight_length (risk : Rat) (depth : Nat) :
    (sourceRight risk depth).length =
      2*(natBits risk.num.natAbs+natBits risk.den+
        (PSTRTMThresholdBBackupEntry188.result risk depth).depth.length+
        natBits (PaperProofs.Statistics.controllerB risk depth)+
        natBits (PSTRTMThresholdBadFactor226.factor risk depth))+
        2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap+12 := by
  simp only [sourceRight,locatorRight,PSTRTMThresholdBadSource229.sourceRight,markerTail,
    List.length_append,List.length_cons,List.length_replicate,
    PSTRTMIncrement009.blocks_length,numerator,denominator,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  omega

private theorem arithmetic_packet (input depth numeratorDen depthWidth boundWidth factorWidth gap : Nat)
    (hnd : numeratorDen ≤ input+1) (hd : depthWidth ≤ input+1)
    (hb : boundWidth ≤ input+4) (hf : factorWidth ≤ input+6)
    (hg : gap ≤ 64*(input+depth+1)^2) :
    2*(numeratorDen+depthWidth+boundWidth+factorWidth)+2*gap+12 ≤ 256*(input+depth+1)^2 := by
  have hp : input+1 ≤ (input+depth+1)^2 := by
    have hs : 1 ≤ input+depth+1 := by omega
    have hc := Nat.pow_le_pow_right hs (by decide : 1 ≤ 2)
    simp only [pow_one] at hc
    omega
  omega

/-- Actual retained packet width, derived from ORIGINAL input fields and
the actual loop-created gap. This is not an extra original input bound. -/
theorem sourceRight_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    (sourceRight risk depth).length ≤
      256*((encode [.rational risk,.natural depth]).length+depth+1)^2 := by
  have hnd := PSTRTMThresholdRisk114.original_widths_le risk depth hr
  have hdepth := PSTRTMThresholdBackup139.original_width_le risk depth hr
  rw [PSTRTMThresholdDepthSource184.depth_length] at hdepth
  have hresult := PSTRTMThresholdRiskReturnBudget230.result_depth_length risk depth hd
  have ht : (PSTRTMThresholdBBackupEntry188.result risk depth).depth.length ≤
      (encode [.rational risk,.natural depth]).length+1 := by omega
  have hb := PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  have hf := PSTRTMThresholdBadFactor226.factor_bits_le risk depth hr hd
  have hg := PSTRTMThresholdRiskReturnBudget230.result_gap_le risk depth hr hd
  rw [sourceRight_length]
  exact arithmetic_packet _ _ _ _ _ _ _ hnd ht hb hf hg

private theorem arithmetic_time (input depth width main : Nat)
    (hm : main ≤ 100663296*(input+depth+1)^3) (hw : width ≤ input+1) :
    main+2*width+16 ≤ 134217728*(input+depth+1)^3 := by
  have hs : 1 ≤ input+depth+1 := by omega
  have hc : input+1 ≤ (input+depth+1)^3 := by
    have hp := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
    simp only [pow_one] at hp
    omega
  omega

private theorem scale_cube (input depth : Nat) : input+1 ≤ (input+depth+1)^3 := by
  have hs : 1 ≤ input+depth+1 := by omega
  have hp := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hp
  omega

theorem original_riskSource_contract (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    ∃ trace last, Runs riskSourceMachine (encode [.rational risk,.natural depth]) trace last ∧
      last.Tape = Turing.Tape.mk₂ [false] (sourceRight risk depth) ∧
      trace.length ≤ 134217728*((encode [.rational risk,.natural depth]).length+depth+1)^3 ∧
      ∀ clock, visitedSpace riskSourceMachine (encode [.rational risk,.natural depth]).length (trace.take clock) ≤
        536870912*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  obtain ⟨before,first,hfirst,htape,htime,_⟩ := original_locator_contract risk depth hr hd
  let part := riskFieldsTrace [] (numerator risk) (denominator risk) (locatorRight risk depth)
  let trace := before.map (PSTRTMSeq005.leftCfg (b := 17)) ++
    part.map (PSTRTMSeq005.rightCfg (a := 1346))
  let last := PSTRTMSeq005.rightCfg (a := 1346)
    (riskFieldsFinal [] (numerator risk) (denominator risk) (locatorRight risk depth))
  have hrun : Runs riskSourceMachine (encode [.rational risk,.natural depth]) trace last := by
    apply PSTRTMSeq005.seq_runs locatorMachine riskFieldsMachine
      (encode [.rational risk,.natural depth]) first
      (riskFieldsFinal [] (numerator risk) (denominator risk) (locatorRight risk depth))
      before part hfirst
    rw [htape,original_marker_entry]
    exact riskFields_runsFrom _ _ _ _
  have hout : last.Tape = Turing.Tape.mk₂ [false] (sourceRight risk depth) := rfl
  have hfulltime : trace.length ≤ 134217728*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
    have hw := PSTRTMThresholdRisk114.original_widths_le risk depth hr
    have hcost := arithmetic_time (encode [.rational risk,.natural depth]).length depth
      (natBits risk.num.natAbs+natBits risk.den) before.length htime hw
    simpa only [trace,part,List.length_append,List.length_map,riskFields_length,
      numerator,denominator,PSTRTMNatValue017.rawPayload,List.length_ofFn,Nat.add_assoc] using hcost
  refine ⟨trace,last,hrun,hout,hfulltime,?_⟩
  intro clock
  have hs := PSTRTMTrace002.visitedSpace_le riskSourceMachine
    (encode [.rational risk,.natural depth]).length (trace.take clock)
  have hl : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hc := scale_cube (encode [.rational risk,.natural depth]).length depth
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRiskSource233
