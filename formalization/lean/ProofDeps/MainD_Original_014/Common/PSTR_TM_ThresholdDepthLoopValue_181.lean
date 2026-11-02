module
public import Common.PSTR_TM_ThresholdDepthLoopRun_180

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopValue181
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthLoopTrace179 PSTRTMThresholdDepthLoopNext177
open PSTRTMThresholdCountdownCode164

def advance : Nat → Nat → Nat
  | 0,value => value
  | count+1,value => advance count (nextValue value)

/-- The proof-only endpoint has exactly the unchanged physical depth
width, a genuinely exhausted counter, and precisely depth-1 Bnext calls.
These are invariants of the SAME fixed machine and actual trace180. -/
theorem outcome_properties (depth : List Bool) (value gap : Nat) (hp : true∈depth) :
    (outcome depth value gap).depth.length=depth.length ∧
    PSTRTMIncrement009.valueDigits (outcome depth value gap).depth=0 ∧
    (outcome depth value gap).value=advance (PSTRTMIncrement009.valueDigits depth-1) value := by
  by_cases hv : PSTRTMIncrement009.valueDigits depth=1
  · rw [outcome_zero depth value gap hp hv]
    have hpred := pred_value depth hp
    refine ⟨pred_length depth,?_,?_⟩
    · change PSTRTMIncrement009.valueDigits (predDigits depth)=0
      omega
    · simp only [hv,Nat.sub_self,advance]
  · rw [outcome_step depth value gap hp hv]
    have hrec := outcome_properties (predDigits depth) (nextValue value) (nextGap value gap)
      (pred_positive depth hp hv)
    have hpred := pred_value depth hp
    have hpos : 0 < PSTRTMIncrement009.valueDigits (predDigits depth) := by omega
    have he : PSTRTMIncrement009.valueDigits depth-1=
        (PSTRTMIncrement009.valueDigits (predDigits depth)-1)+1 := by omega
    exact ⟨hrec.1.trans (pred_length depth),hrec.2.1,by rw [he,advance]; exact hrec.2.2⟩
termination_by PSTRTMIncrement009.valueDigits depth
decreasing_by
  have h := pred_value depth hp
  omega

theorem nextValue_le_max (value : Nat) : nextValue value≤max value 2 := by
  have hm := Nat.le_max_left value 2
  calc
    nextValue value≤Nat.clog 2 (2+max value 2) := Nat.clog_mono_right 2 (by omega)
    _≤max value 2 := PaperProofs.Statistics.clog_two_add_le _ (Nat.le_max_right _ _)

theorem nextValue_le_bound (value bound : Nat) (hv : value≤bound) (hb : 2≤bound) :
    nextValue value≤bound := (nextValue_le_max value).trans (max_le hv hb)

theorem advance_le_bound (count value bound : Nat) (hv : value≤bound) (hb : 2≤bound) :
    advance count value≤bound := by
  induction count generalizing value with
  | zero => exact hv
  | succ count ih => exact ih _ (nextValue_le_bound _ _ hv hb)

/-- The original recurrence at indices at least ONE; no risk quarter
qualification is added to the original general positive-risk input. -/
theorem advance_controllerB (risk : Rat) (index count : Nat) (hi : 1 ≤ index) :
    advance count (PaperProofs.Statistics.controllerB risk index)=
      PaperProofs.Statistics.controllerB risk (index+count) := by
  induction count generalizing index with
  | zero => simp only [advance,Nat.add_zero]
  | succ count ih =>
    rw [advance]
    have hn : nextValue (PaperProofs.Statistics.controllerB risk index)=
        PaperProofs.Statistics.controllerB risk (index+1) := by
      simpa only [nextValue,Nat.add_comm] using (PaperProofs.Statistics.controllerB_succ risk index hi).symm
    rw [hn,ih (index+1) (by omega)]
    congr 1
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopValue181
