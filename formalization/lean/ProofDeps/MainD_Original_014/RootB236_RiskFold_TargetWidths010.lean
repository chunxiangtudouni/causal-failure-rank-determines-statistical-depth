module

public import RootB236_RiskFold_Import003

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB236.RiskFold

open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation PaperProofs.Statistics

theorem half_width (risk : Rat) :
    RatInput.Encoder.fieldSize (risk/2)≤RatInput.Encoder.fieldSize risk+3 := by
  have value : risk/2=risk*(1/2) := by ring
  have half : RatInput.Encoder.fieldSize (1/(2 : Rat))=3 := by
    rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    norm_num [RootB23.WordOddsBits.width,natBits]
  rw [value]
  simpa only [half] using RootB234.ECost.mul_field risk (1/2)

theorem threshold_input_length (risk : Rat) (depth : Nat) :
    (encode [.rational risk,.natural depth]).length=
      2*RatInput.Encoder.fieldSize risk+2*natBits depth+12 := by
  simp only [encode,List.length_append,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
    PSTRTMLength004.encodeNat_length,PSTRTMLength004.encodeDatum_rational_length,
    PSTRTMLength004.encodeDatum_natural_length]
  rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
  unfold RootB23.WordOddsBits.width
  have two : natBits 2=2 := rfl
  rw [two]
  omega

theorem threshold_scale (risk : Rat) (depth : Nat) :
    RootB23.Threshold.OriginalBridge.scale risk depth≤2*RatInput.Encoder.fieldSize risk+3*depth+15 := by
  have digits := RootB234.ECost.raw_length depth
  simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn] at digits
  unfold RootB23.Threshold.OriginalBridge.scale
  rw [threshold_input_length]
  omega

theorem target_width (risk : Rat) (depth : Nat) (positive : 0<risk) (depthPositive : 1≤depth) :
    RatInput.Encoder.fieldSize (controllerTarget risk depth)≤
      128*(2*RatInput.Encoder.fieldSize risk+3*depth+15) := by
  have total := RootB23.Threshold.FinalSemantics.nine_width_le risk depth positive depthPositive
  have part : RatInput.Encoder.fieldSize (controllerTarget risk depth)≤
      RootB23.Threshold.FinalSerialize.totalWidth (controllerB risk depth) (controllerTarget risk depth)
        (controllerBadRisk risk (controllerTarget risk depth))
        ((1-controllerTarget risk depth)/controllerTarget risk depth)
        (controllerTarget risk depth/(1-controllerTarget risk depth)) := by
    simp only [RatInput.Encoder.fieldSize,RootB23.Threshold.FinalSerialize.totalWidth,
      RootB23.Threshold.FinalSerialize.nineFields,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega
  have scale := threshold_scale risk depth
  change RootB23.Threshold.FinalSemantics.inputScale risk depth≤_ at scale
  exact part.trans ((Nat.le_add_right _ 1).trans total |>.trans (Nat.mul_le_mul_left 128 scale))

def caseDepth : ReferenceBudgetCase → Nat
  | .infiniteRank | .noTool => 0
  | .finiteBad depth => depth.val

theorem original_target_width (budget : Rat) (events : List ReferenceBudgetEvent)
    (kind : ReferenceBudgetCase) (target : Rat) (valid : 0<budget ∧ budget≤1/2)
    (actual : (referenceBudgetPath (budget/2) events).bind (referenceBudgetTarget kind)=some target) :
    RatInput.Encoder.fieldSize target≤
      128*(4*RatInput.Encoder.fieldSize budget+12*events.length+3*caseDepth kind+23) := by
  obtain ⟨current,path,selected⟩ := Option.bind_eq_some_iff.mp actual
  have width := original_path_width budget events current valid path
  cases kind with
  | infiniteRank => cases selected
  | noTool =>
      have same : current/2=target := Option.some.inj selected
      subst target
      have half := half_width current
      change RatInput.Encoder.fieldSize (current/2)≤
        128*(4*RatInput.Encoder.fieldSize budget+12*events.length+3*0+23)
      omega
  | finiteBad depth =>
      have same : controllerTarget current depth.val=target := Option.some.inj selected
      subst target
      have initial : ReferenceBudgetValid (budget/2) := by constructor <;> linarith [valid.1,valid.2]
      have positive := (referenceBudgetPath_valid_floor events (budget/2) current initial path).1.1
      have field := target_width current depth.val positive depth.pos
      change RatInput.Encoder.fieldSize (controllerTarget current depth.val)≤
        128*(4*RatInput.Encoder.fieldSize budget+12*events.length+3*depth.val+23)
      omega

end RootB236.RiskFold
