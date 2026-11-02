module
public import Structure.RootB23_Threshold_Uncapped_Fields_002
public import Structure.RootB23_Threshold_Uncapped_Clean_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section
namespace RootB23.Threshold.Uncapped.Restore
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBBackupEntry188

def captureCode : Machine 17 := PSTRTMSeq005.seqMachine BReturn.returnMachine PSTRTMThresholdRiskReturn228.depthMachine
def code : Machine 35 := PSTRTMSeq005.seqMachine captureCode PSTRTMThresholdRiskMarkers232.riskFieldsMachine
def inputSize (q : Rat) : Nat := (encode [.rational q,.natural 1]).length

theorem intrinsic_fields (q : Rat) (hq : 0 < q) :
    (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB q 1)).length ≤ inputSize q+4 ∧
    (result q 1).depth.length = 1 ∧
    (result q 1).gap ≤ 64*(inputSize q+2)^2 ∧
    (PSTRTMNatValue017.rawPayload q.num.natAbs).length+
      (PSTRTMNatValue017.rawPayload q.den).length ≤ inputSize q+1 := by
  have hb := PSTRTMThresholdBBackupCost189.controllerB_bits_le q 1 hq (by decide)
  have hd := PSTRTMThresholdRiskReturnBudget230.result_depth_length q 1 (by decide)
  have hg := PSTRTMThresholdRiskReturnBudget230.result_gap_le q 1 hq (by decide)
  have hw := PSTRTMThresholdRisk114.original_widths_le q 1 hq
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [PSTRTMNatValue017.rawPayload,List.length_ofFn,inputSize] using hb
  · have one : natBits 1 = 1 := by decide
    exact hd.trans one
  · exact hg
  · simpa only [PSTRTMNatValue017.rawPayload,List.length_ofFn,inputSize] using hw

/-- A new suffix runs on the exact real FALSE tape of245, rather than
rerunning245 or assuming a prepared window/NUM/DEN answer. The q archive,
DEPTH flags, cleared gap and BOTH B fields are moved literally. -/
theorem false_archive_contract (q : Rat) (hq : 0 < q) (uncapped : q < 1/4) :
    ∃ states, PSTRTMSeq005.RunsFrom code
      ⟨0,(PSTRTMThresholdDynamicCap245.final q).Tape⟩ states
      ⟨35,Turing.Tape.mk₂ [false] (Numerator.sourceRight q)⟩ ∧
      states.length ≤ 1024*(inputSize q+2)^2 := by
  let b := PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB q 1)
  let numerator := PSTRTMNatValue017.rawPayload q.num.natAbs
  let denominator := PSTRTMNatValue017.rawPayload q.den
  let middleB := Turing.Tape.mk₂ (false::sourceArchive q 1) (Source.sourceRight q)
  let middleDepth := Turing.Tape.mk₂ (false::PSTRTMThresholdDepthSource184.riskArchive q) (Depth.locatorRight q)
  let finalTape := Turing.Tape.mk₂ [false] (Numerator.sourceRight q)
  have r0 : ∃ states, PSTRTMSeq005.RunsFrom BReturn.returnMachine
      ⟨0,(PSTRTMThresholdDynamicCap245.final q).Tape⟩ states ⟨8,middleB⟩ ∧
      states.length ≤ 2*b.length+8 := by
    refine ⟨BReturn.returnTrace (sourceArchive q 1) b (encodeNat (PaperProofs.Statistics.controllerB q 1)),?_,?_⟩
    · have real := BReturn.return_runsFrom (sourceArchive q 1) b (encodeNat (PaperProofs.Statistics.controllerB q 1))
      have input : (PSTRTMThresholdDynamicCap245.final q).Tape =
          Turing.Tape.mk₂ (PA17TMRatArithmeticCopy006.sourceLeft (sourceArchive q 1) b)
            (false::encodeNat (PaperProofs.Statistics.controllerB q 1)) := by
        rw [PSTRTMThresholdDynamicCap245.final_tape q hq]
        simp only [not_le.mpr uncapped,ite_false,encodeDatum]
        rfl
      rw [input]
      exact real
    · exact (BReturn.return_length _ _ _).le
  have r1 : ∃ states, PSTRTMSeq005.RunsFrom PSTRTMThresholdRiskReturn228.depthMachine
      ⟨0,middleB⟩ states ⟨8,middleDepth⟩ ∧
      states.length ≤ 2*(result q 1).gap+2*(result q 1).depth.length+12 := by
    have nonempty := PSTRTMThresholdRiskReturnBudget230.result_depth_ne_nil q 1 (by decide)
    cases found : (result q 1).depth.reverse with
    | nil =>
      have empty := congrArg List.reverse found
      simp only [List.reverse_reverse,List.reverse_nil] at empty
      exact False.elim (nonempty empty)
    | cons bit earlier =>
      have back : (bit::earlier).reverse = (result q 1).depth := by
        rw [←found,List.reverse_reverse]
      let realGap := 2*(result q 1).gap+2
      refine ⟨PSTRTMThresholdRiskReturn228.depthTrace (PSTRTMThresholdDepthSource184.riskArchive q)
        bit earlier (Source.sourceRight q) realGap,?_,?_⟩
      · have real := PSTRTMThresholdRiskReturn228.depth_runsFrom (PSTRTMThresholdDepthSource184.riskArchive q)
          bit earlier (Source.sourceRight q) realGap
        have input : middleB = Turing.Tape.mk₂
            (List.replicate realGap false++(PSTRTMRawNat010.leftBlocks (bit::earlier)++
              false::PSTRTMThresholdDepthSource184.riskArchive q)) (Source.sourceRight q) := by
          dsimp only [middleB,realGap]
          rw [Source.archive_entry,found]
        rw [input]
        have terminal_port : PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4) = (8 : Fin 9) := by decide
        simpa only [PSTRTMThresholdRiskReturn228.depthFinal,PSTRTMSeq005.rightCfg,
          PSTRTMMulRewind085.state,terminal_port,middleDepth,Depth.locatorRight,back,realGap] using real
      · rw [PSTRTMThresholdRiskReturn228.depth_length]
        have count := congrArg List.length found
        simp only [List.length_reverse,List.length_cons] at count
        dsimp only [realGap]
        omega
  have r01 := Clean.joined_bounded BReturn.returnMachine PSTRTMThresholdRiskReturn228.depthMachine
    (PSTRTMThresholdDynamicCap245.final q).Tape middleB middleDepth
    (2*b.length+8) (2*(result q 1).gap+2*(result q 1).depth.length+12) r0 r1
  have r2 : ∃ states, PSTRTMSeq005.RunsFrom PSTRTMThresholdRiskMarkers232.riskFieldsMachine
      ⟨0,middleDepth⟩ states ⟨17,finalTape⟩ ∧
      states.length ≤ 2*(numerator.length+denominator.length)+16 := by
    refine ⟨PSTRTMThresholdRiskMarkers232.riskFieldsTrace [] numerator denominator (Depth.locatorRight q),?_,?_⟩
    · exact PSTRTMThresholdRiskMarkers232.riskFields_runsFrom [] numerator denominator (Depth.locatorRight q)
    · exact (PSTRTMThresholdRiskMarkers232.riskFields_length _ _ _ _).le
  obtain ⟨states,actual,time⟩ := Clean.joined_bounded captureCode PSTRTMThresholdRiskMarkers232.riskFieldsMachine
    (PSTRTMThresholdDynamicCap245.final q).Tape middleDepth finalTape
    (2*b.length+8+(2*(result q 1).gap+2*(result q 1).depth.length+12))
    (2*(numerator.length+denominator.length)+16) r01 r2
  refine ⟨states,actual,?_⟩
  obtain ⟨hb,hd,hg,hw⟩ := intrinsic_fields q hq
  have hs : 1 ≤ inputSize q+2 := by omega
  have square : inputSize q+2 ≤ (inputSize q+2)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (by decide : 1 ≤ 2)
  dsimp only [b,numerator,denominator] at time
  omega

end RootB23.Threshold.Uncapped.Restore
