module
public import Structure.RootB23_Threshold_Uncapped_Restore_010
public import Structure.RootB23_Threshold_Uncapped_Export_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section
namespace RootB23.Threshold.Uncapped.Recovery
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBBackupEntry188
open PA17TMRatArithmeticPairEncode017

def code : Machine 216 := PSTRTMSeq005.seqMachine Restore.code Export.bareCode

theorem source_word (q : Rat) : Numerator.sourceRight q = Serialize.inputRight q.num.natAbs q.den
    (true::false::Clean.gapRight (result q 1).depth (result q 1).gap
      (PaperProofs.Statistics.controllerB q 1)) := by
  unfold Numerator.sourceRight Serialize.inputRight Serialize.marker Clean.gapRight
    Depth.locatorRight Source.sourceRight Source.digits payload PSTRTMThresholdRiskMarkers232.markerTail
  rw [show 2*(result q 1).gap+2 = 2*((result q 1).gap+1) by omega]
  simp only [List.append_assoc]

theorem source_input (q : Rat) :
    Turing.Tape.mk₂ [false] (Numerator.sourceRight q) =
      Turing.Tape.mk₂ [false,false] (Serialize.inputRight q.num.natAbs q.den
        (true::false::Clean.gapRight (result q 1).depth (result q 1).gap
          (PaperProofs.Statistics.controllerB q 1))) := by
  rw [source_word]
  simp only [Turing.Tape.mk₂]
  rw [show Turing.ListBlank.mk [false,false] = Turing.ListBlank.mk [false] from
    PSTRTMRawNat010.blank_append_false [false]]

/-- Complete actual FALSE suffix from245's real endpoint. All scratch
and markers are physically discharged before q is serialized. The blank
left side here is proved by the original q source producer, not an entry
workspace qualification or a supplied finished output. -/
theorem false_suffix_contract (q : Rat) (hq : 0 < q) (uncapped : q < 1/4) :
    ∃ states, PSTRTMSeq005.RunsFrom code
      ⟨0,(PSTRTMThresholdDynamicCap245.final q).Tape⟩ states
      ⟨216,Turing.Tape.mk₁ (encodeDatum (.rational q))⟩ ∧
      states.length ≤ 8192*(Restore.inputSize q+2)^2 := by
  let middle := Turing.Tape.mk₂ [false] (Numerator.sourceRight q)
  let tailCost := Export.tailCost (result q 1).depth (result q 1).gap
    (PaperProofs.Statistics.controllerB q 1) q.num.natAbs q.den+
      128*(natBits q.num.natAbs+natBits q.den+1)^2
  have firstRun := Restore.false_archive_contract q hq uncapped
  have secondRun : ∃ states, PSTRTMSeq005.RunsFrom Export.bareCode ⟨0,middle⟩ states
      ⟨180,Turing.Tape.mk₁ (encodeDatum (.rational q))⟩ ∧ states.length ≤ tailCost := by
    have real := Export.bare_contract [] (result q 1).depth (result q 1).gap
      (PaperProofs.Statistics.controllerB q 1) q hq
    rw [←source_input] at real
    exact real
  obtain ⟨states,actual,time⟩ := Clean.joined_bounded Restore.code Export.bareCode
    (PSTRTMThresholdDynamicCap245.final q).Tape middle (Turing.Tape.mk₁ (encodeDatum (.rational q)))
    (1024*(Restore.inputSize q+2)^2) tailCost firstRun secondRun
  refine ⟨states,actual,?_⟩
  obtain ⟨hb,hd,hg,hw⟩ := Restore.intrinsic_fields q hq
  have hb2 : (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB q 1)).length ≤
      2*(Restore.inputSize q+2) := by omega
  have bsquare : (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB q 1)).length^2 ≤
      4*(Restore.inputSize q+2)^2 := by
    have square := Nat.pow_le_pow_left hb2 2
    nlinarith
  have widths : natBits q.num.natAbs+natBits q.den+1 ≤ Restore.inputSize q+2 := by
    simpa only [PSTRTMNatValue017.rawPayload,List.length_ofFn] using Nat.add_le_add_right hw 1
  have wsquare := Nat.pow_le_pow_left widths 2
  have hs : 1 ≤ Restore.inputSize q+2 := by omega
  have square : Restore.inputSize q+2 ≤ (Restore.inputSize q+2)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (by decide : 1 ≤ 2)
  dsimp only [tailCost,Export.tailCost,payload] at time
  omega

end RootB23.Threshold.Uncapped.Recovery
