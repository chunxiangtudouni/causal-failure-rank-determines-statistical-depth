module
public import Structure.RootB23_Threshold_Spatial_MulCap_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnCredit
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticParse002

private theorem left_length (digits : List Bool) :
    (PSTRTMRawNat010.leftBlocks digits).length=2*digits.length := by
  induction digits with
  | nil=>rfl
  | cons bit later ih=>
    simp only [PSTRTMRawNat010.leftBlocks,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at ih ⊢
    omega

theorem savedLeft_length (q : Rat) :
    (PSTRTMThresholdBReblock195.savedLeft q 1).length=
      2*natBits (PaperProofs.Statistics.controllerB q 1)+
      2*(PSTRTMThresholdBBackupEntry188.result q 1).gap+
      2*(PSTRTMThresholdBBackupEntry188.result q 1).depth.length+
      2*(natBits q.num.natAbs+natBits q.den)+12 := by
  simp only [PSTRTMThresholdBReblock195.savedLeft,PA17TMRatArithmeticCopy006.sourceLeft,
    PSTRTMThresholdBBackupEntry188.sourceArchive,PSTRTMThresholdDepthSource184.riskArchive,
    PSTRTMThresholdDenPrepare141.denArchive,PSTRTMThresholdCounterSeek169.gaps_replicate,
    List.length_cons,List.length_append,List.length_nil,left_length,List.length_reverse,
    List.length_replicate,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  omega

theorem depth_one_gap (q : Rat) :
    (PSTRTMThresholdBBackupEntry188.result q 1).gap=PSTRTMThresholdDepthSource184.initialGap q := by
  exact congrArg PSTRTMThresholdDepthLoopTrace179.Outcome.gap
    (PSTRTMThresholdDepthLoopTrace179.outcome_zero (PSTRTMThresholdBackup139.depthDigits 1)
      (PaperProofs.Statistics.controllerB q 1) (PSTRTMThresholdDepthSource184.initialGap q)
      (PSTRTMThresholdDepthSource184.depth_positive 1 (by decide))
      (PSTRTMThresholdDepthSource184.depth_value 1))

theorem savedLeft_cap_length_le (q : Rat) (positive : 0<q) :
    (PSTRTMThresholdBReblock195.savedLeft q 1).length≤
      8*(encode [.rational q,.natural 1]).length+64 := by
  have b:=PSTRTMThresholdBBackupCost189.controllerB_bits_le q 1 positive (by decide)
  have gap:=PSTRTMThresholdDepthSource184.original_gap_le q 1 positive
  have depth:=PSTRTMThresholdRiskReturnBudget230.result_depth_length q 1 (by decide)
  have risk:=PSTRTMThresholdRisk114.original_widths_le q 1 positive
  have one : natBits 1=1 := by decide
  rw [one] at depth
  rw [savedLeft_length,depth_one_gap,depth]
  omega

/-- An explicit linear reserve sufficient to retain ALL true cap source
cells in Frame005.windowPrefix, not an assertion that they are blank. -/
def spare (x y : Rat) : ℕ := 32*fieldWidth x y+512

theorem oldLeft_fits (x y : Rat) (positive : 0<x*y) :
    (Spatial.MulCap.oldLeft x y).length≤spare x y := by
  by_cases capped : (1/4 : Rat)≤x*y
  · simp only [Spatial.MulCap.oldLeft,capped,ite_true]
    have old:=savedLeft_cap_length_le (x*y) positive
    have raw:=PaperProofs.Common.Native.RationalControllerComputation.RootB23.Threshold.Spatial.raw_product_length_le x y
    have packet:=Spatial.MulCap.cap_packet_length (x*y)
    have input:=pair_length x y
    change (encode [.rational x,.rational y]).length=2*fieldWidth x y+14 at input
    change (encode [.rational (x*y)]).length≤2*(encode [.rational x,.rational y]).length at raw
    unfold spare
    omega
  · simp only [Spatial.MulCap.oldLeft,capped,ite_false,List.length_nil]
    exact Nat.zero_le _

theorem prefix_complete (x y : Rat) (positive : 0<x*y) (left : ℕ) (room : spare x y≤left) :
    PA17TMRatArithmeticFrame005.windowPrefix left (ListBlank.mk (Spatial.MulCap.oldLeft x y))=
      Spatial.MulCap.oldLeft x y++List.replicate (left-(Spatial.MulCap.oldLeft x y).length) false :=
  PA17TMRatArithmeticFrame005.windowPrefix_mk_of_length _ _ ((oldLeft_fits x y positive).trans room)

end RootB23.Threshold.ReturnCredit
