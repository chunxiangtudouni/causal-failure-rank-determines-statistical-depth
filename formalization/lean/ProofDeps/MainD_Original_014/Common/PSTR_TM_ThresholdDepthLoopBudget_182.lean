module
public import Common.PSTR_TM_ThresholdDepthLoopValue_181

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopBudget182
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthLoopNext177 PSTRTMThresholdDepthLoopValue181

/-- Ghost potential for the SAME actual physical loop layout. Width
is derived from a bound on the initial B, never supplied to the program.
The last term pays for the real cleared-gap growth on every iteration. -/
def phaseBudget (width fieldLength gap remaining : Nat) : Nat :=
  4*gap+9*fieldLength+19+32768*width^2+32*width*remaining

theorem bound_bits_two (bound : Nat) (hb : 2≤bound) : 2≤natBits bound := by
  have h := PSTRTMArithmetic008.natBits_mono hb
  have ht : natBits 2=2 := by decide
  rw [ht] at h
  exact h

theorem nextGap_le (value bound gap : Nat) (hv : value≤bound) (hb : 2≤bound) :
    nextGap value gap≤gap+7*natBits bound := by
  have hw := PSTRTMB1RunFrame122.width_le 1 (value+2)
  have ha := PSTRTMArithmetic008.natBits_add_le value 2
  have hvBits := PSTRTMArithmetic008.natBits_mono hv
  have hp := bound_bits_two bound hb
  have ho : natBits 1=1 := by decide
  have ht : natBits 2=2 := by decide
  rw [ho] at hw
  rw [ht] at ha
  unfold nextGap
  omega

theorem square_cost_le (value bound : Nat) (hv : value≤bound) (hb : 2≤bound) :
    8192*(natBits value+1)^2≤32768*(natBits bound)^2 := by
  have hm := PSTRTMArithmetic008.natBits_mono hv
  have hp := bound_bits_two bound hb
  have he : natBits value+1≤2*natBits bound := by omega
  have he2 := Nat.pow_le_pow_left he 2
  nlinarith

theorem positive_length_budget (archive depth : List Bool) (value bound gap : Nat)
    (hp : true∈depth) (hv : value≤bound) (hb : 2≤bound) :
    (PSTRTMThresholdDepthLoopPositive178.positiveTrace archive depth value gap).length≤
      phaseBudget (natBits bound) depth.length gap (PSTRTMIncrement009.valueDigits depth) := by
  have ht := PSTRTMThresholdDepthLoopPositive178.positive_length_le archive depth value gap hp
  have hs := square_cost_le value bound hv hb
  unfold phaseBudget
  omega

theorem zero_length_budget (archive depth : List Bool) (value bound gap : Nat) (hp : true∈depth) :
    (PSTRTMThresholdDepthLoopZero176.zeroTrace archive depth value gap).length≤
      phaseBudget (natBits bound) depth.length gap (PSTRTMIncrement009.valueDigits depth) := by
  have ht := PSTRTMThresholdDepthLoopZero176.zero_length_le archive depth value gap hp
  unfold phaseBudget
  omega

theorem phaseBudget_decreases (width fieldLength gap nextGap remaining nextRemaining : Nat)
    (hg : nextGap≤gap+7*width) (hr : nextRemaining+1=remaining) :
    phaseBudget width fieldLength nextGap nextRemaining≤phaseBudget width fieldLength gap remaining := by
  rw [←hr]
  unfold phaseBudget
  nlinarith

theorem recurse_cost (remaining nextRemaining budget phase tail : Nat)
    (hr : nextRemaining+1=remaining) (hp : phase≤budget) (ht : tail≤nextRemaining*budget) :
    phase+tail≤remaining*budget := by
  rw [←hr]
  nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopBudget182
