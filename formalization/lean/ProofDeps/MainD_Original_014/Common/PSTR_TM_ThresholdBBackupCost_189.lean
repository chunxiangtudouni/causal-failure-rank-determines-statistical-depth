module
public import Common.PSTR_TM_ThresholdBBackupEntry_188

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBBackupCost189
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBBackupEntry188

theorem controllerB_bits_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1≤depth) :
    natBits (PaperProofs.Statistics.controllerB risk depth)≤(encode [.rational risk,.natural depth]).length+4 := by
  have hb := PSTRTMThresholdDepthLoopValue181.advance_le_bound (depth-1)
    (PaperProofs.Statistics.controllerB risk 1) (max (PaperProofs.Statistics.controllerB risk 1) 2)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have he := PSTRTMThresholdDepthLoopValue181.advance_controllerB risk 1 (depth-1) (by decide)
  have hn : 1+(depth-1)=depth := by omega
  rw [hn] at he
  rw [he] at hb
  exact (PSTRTMArithmetic008.natBits_mono hb).trans
    (PSTRTMThresholdDepthSource184.original_bound_bits_le risk depth hr)

private theorem scale_cube (input depth : Nat) : input+1≤(input+depth+1)^3 := by
  have hp : 1 ≤ input+depth+1 := by omega
  have hp2 : input+depth+1≤(input+depth+1)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (input+depth+1) hp
  have hp3 : (input+depth+1)^2≤(input+depth+1)^3 := by
    exact Nat.pow_le_pow_right hp (by decide : 2≤3)
  omega

private theorem arithmetic_time (input depth main footer : Nat)
    (hm : main≤2097152*(input+depth+1)^3) (hf : footer≤2*input+11) :
    main+footer≤4194304*(input+depth+1)^3 := by
  have hp := scale_cube input depth
  omega

theorem entry_length_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1≤depth) :
    (entryTrace risk depth).length≤4194304*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have hm := PSTRTMThresholdDepthCost186.depth_length_le risk depth hr hd
  have hf := PSTRTMThresholdBFooter187.footer_length (sourceArchive risk depth) []
    (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))
  have hl : (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)).length=
      natBits (PaperProofs.Statistics.controllerB risk depth) := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  rw [hl] at hf
  have hb := controllerB_bits_le risk depth hr hd
  have hfooter : (PSTRTMThresholdBFooter187.footerTrace (sourceArchive risk depth) []
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))).length≤
        2*(encode [.rational risk,.natural depth]).length+11 := by omega
  simp only [entryTrace,List.length_append,List.length_map]
  exact arithmetic_time _ _ _ _ hm hfooter

theorem entry_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1≤depth) :
    visitedSpace entryMachine (encode [.rational risk,.natural depth]).length (entryTrace risk depth)≤
      16777216*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  have ht := entry_length_le risk depth hr hd
  have hs := PSTRTMTrace002.visitedSpace_le entryMachine (encode [.rational risk,.natural depth]).length (entryTrace risk depth)
  have hp := scale_cube (encode [.rational risk,.natural depth]).length depth
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBBackupCost189
