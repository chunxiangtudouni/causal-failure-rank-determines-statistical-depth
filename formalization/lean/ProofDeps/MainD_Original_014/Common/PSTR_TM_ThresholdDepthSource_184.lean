module
public import Common.PSTR_TM_ThresholdDepthLoopCost_183
public import Common.PSTR_TM_ThresholdSeed_155

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthSource184
open PaperProofs.Common.Native.RationalControllerComputation

/-- Actual retained NUM/DEN source cells beyond the DEPTH false guard.
It is obtained from seed155, rather than supplied as a caller field. -/
def riskArchive (risk : Rat) : List Bool :=
  true::false::false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload risk.den).reverse++
    false::PSTRTMThresholdDenPrepare141.denArchive [] (PSTRTMNatValue017.rawPayload risk.num.natAbs))

def initialGap (risk : Rat) : Nat := 2*PSTRTMB1RunFrame122.width risk.num.natAbs risk.den+2

theorem depth_value (depth : Nat) :
    PSTRTMIncrement009.valueDigits (PSTRTMThresholdBackup139.depthDigits depth)=depth :=
  PSTRTMNatValue017.valueDigits_rawPayload depth

theorem depth_length (depth : Nat) : (PSTRTMThresholdBackup139.depthDigits depth).length=natBits depth := by
  simp only [PSTRTMThresholdBackup139.depthDigits,PSTRTMThresholdSource125.depthDigits,
    PSTRTMNatValue017.rawPayload,List.length_ofFn]

theorem depth_positive (depth : Nat) (hd : 1≤depth) : true∈PSTRTMThresholdBackup139.depthDigits depth := by
  apply PSTRTMThresholdCountdownCode164.has_true_of_value_pos
  rw [depth_value]
  omega

/-- ENTIRE actual boundary: seed155 HALT and loop173 q0 share the
same tape and cursor. The actual sequencer still charges its write
transition; this equality does not teleport the head or rebuild data. -/
theorem seed_entry_tape (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    (PSTRTMThresholdSeed155.seedFinal risk depth).Tape=Turing.Tape.mk₂
      (PSTRTMThresholdDepthEntry171.initialLeft (riskArchive risk)
        (PSTRTMThresholdBackup139.depthDigits depth) (initialGap risk+1))
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk 1))) := by
  rw [PSTRTMThresholdSeed155.seed_final_tape risk depth hr]
  congr 1
  let width := PSTRTMB1RunFrame122.width risk.num.natAbs risk.den
  let tail := PSTRTMRawNat010.leftBlocks (PSTRTMThresholdBackup139.depthDigits depth).reverse++false::riskArchive risk
  change List.replicate (4*width+5) false++false::tail=
    PSTRTMThresholdCounterSeek169.gaps (2*width+2+1)++tail
  rw [PSTRTMThresholdCounterSeek169.gaps_replicate]
  have he : 4*width+5+1=2*(2*width+2+1) := by omega
  calc
    List.replicate (4*width+5) false++false::tail=
        (List.replicate (4*width+5) false++[false])++tail := by
          simp only [List.append_assoc,List.singleton_append]
    _=List.replicate (4*width+5+1) false++tail := by rw [←List.replicate_succ']
    _=List.replicate (2*(2*width+2+1)) false++tail := by rw [he]

theorem original_B_one_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    PaperProofs.Statistics.controllerB risk 1≤(encode [.rational risk,.natural depth]).length+1 := by
  have hb : PaperProofs.Statistics.controllerB risk 1=PSTRTMB1Value068.exponent risk.num.natAbs risk.den := by
    conv_lhs => rw [PSTRTMThresholdSeed155.positive_ratio risk hr]
    exact PSTRTMB1Value068.controllerB_one_ratio _ _
  rw [hb]
  have he := PSTRTMB1Value068.exponent_le_bits risk.num.natAbs risk.den
    (PSTRTMThresholdSeed155.numerator_pos risk hr)
  have hw := PSTRTMThresholdRisk114.original_widths_le risk depth hr
  omega

theorem original_gap_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    initialGap risk≤2*(encode [.rational risk,.natural depth]).length+6 := by
  have hg := PSTRTMB1RunFrame122.width_le risk.num.natAbs risk.den
  have hw := PSTRTMThresholdRisk114.original_widths_le risk depth hr
  unfold initialGap
  omega

theorem original_bound_bits_le (risk : Rat) (depth : Nat) (hr : 0 < risk) :
    natBits (max (PaperProofs.Statistics.controllerB risk 1) 2)≤
      (encode [.rational risk,.natural depth]).length+4 := by
  have hb := original_B_one_le risk depth hr
  have hm : max (PaperProofs.Statistics.controllerB risk 1) 2≤
      (encode [.rational risk,.natural depth]).length+3 := max_le (by omega) (by omega)
  have hl := Nat.log2_le_self (max (PaperProofs.Statistics.controllerB risk 1) 2)
  unfold natBits
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthSource184
