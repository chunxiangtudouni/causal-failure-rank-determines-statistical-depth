module
public import Common.PSTR_TM_ThresholdDepthLoopPositive_178

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopTrace179
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCountdownCode164 PSTRTMThresholdDepthLoopNext177

/-- Proof-only endpoint of the fixed388-label loop. None of these
fields selects a program or is supplied to the original input. The
recursive decrease is the value of the physically decremented field. -/
structure Outcome where
  depth : List Bool
  value : Nat
  gap : Nat

def outcome (depth : List Bool) (value gap : Nat) : Outcome :=
  if _hp : true∈depth then
    if PSTRTMIncrement009.valueDigits depth=1 then ⟨predDigits depth,value,gap⟩
    else outcome (predDigits depth) (nextValue value) (nextGap value gap)
  else ⟨depth,value,gap⟩
termination_by PSTRTMIncrement009.valueDigits depth
decreasing_by
  have h := pred_value depth _hp
  omega

/-- A ghost list of ACTUAL configurations of the one fixed machine.
The positive case overlaps the IDENTICAL q0 endpoint. Its real write
transition into q0 is already present in positiveTrace178. Membership
tests below define this proof witness, not the machine's control. -/
def loopTrace (archive depth : List Bool) (value gap : Nat) : List (MachineState 387) :=
  if _hp : true∈depth then
    if PSTRTMIncrement009.valueDigits depth=1 then
      PSTRTMThresholdDepthLoopZero176.zeroTrace archive depth value gap
    else PSTRTMOverlap132.glue
      (PSTRTMThresholdDepthLoopPositive178.positiveTrace archive depth value gap)
      (loopTrace archive (predDigits depth) (nextValue value) (nextGap value gap))
  else []
termination_by PSTRTMIncrement009.valueDigits depth
decreasing_by
  have h := pred_value depth _hp
  omega

def loopFinal (archive depth : List Bool) (value gap : Nat) : MachineState 387 :=
  let result := outcome depth value gap
  PSTRTMThresholdDepthLoopCode173.final (Turing.Tape.mk₂
    (PSTRTMThresholdDepthEntry171.initialLeft archive result.depth (result.gap+1))
    (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload result.value)))

theorem outcome_zero (depth : List Bool) (value gap : Nat) (hp : true∈depth)
    (hv : PSTRTMIncrement009.valueDigits depth=1) :
    outcome depth value gap=⟨predDigits depth,value,gap⟩ := by
  rw [outcome,dite_eq_left hp,ite_eq_left hv]

theorem outcome_step (depth : List Bool) (value gap : Nat) (hp : true∈depth)
    (hv : PSTRTMIncrement009.valueDigits depth≠1) :
    outcome depth value gap=outcome (predDigits depth) (nextValue value) (nextGap value gap) := by
  rw [outcome,dite_eq_left hp,ite_eq_right hv]

theorem loopTrace_zero (archive depth : List Bool) (value gap : Nat) (hp : true∈depth)
    (hv : PSTRTMIncrement009.valueDigits depth=1) :
    loopTrace archive depth value gap=PSTRTMThresholdDepthLoopZero176.zeroTrace archive depth value gap := by
  rw [loopTrace,dite_eq_left hp,ite_eq_left hv]

theorem loopTrace_step (archive depth : List Bool) (value gap : Nat) (hp : true∈depth)
    (hv : PSTRTMIncrement009.valueDigits depth≠1) :
    loopTrace archive depth value gap=PSTRTMOverlap132.glue
      (PSTRTMThresholdDepthLoopPositive178.positiveTrace archive depth value gap)
      (loopTrace archive (predDigits depth) (nextValue value) (nextGap value gap)) := by
  rw [loopTrace,dite_eq_left hp,ite_eq_right hv]

theorem pred_positive (depth : List Bool) (hp : true∈depth)
    (hv : PSTRTMIncrement009.valueDigits depth≠1) : true∈predDigits depth := by
  apply has_true_of_value_pos
  have h := pred_value depth hp
  omega

theorem loopFinal_step (archive depth : List Bool) (value gap : Nat) (hp : true∈depth)
    (hv : PSTRTMIncrement009.valueDigits depth≠1) :
    loopFinal archive depth value gap=loopFinal archive (predDigits depth) (nextValue value) (nextGap value gap) := by
  simp only [loopFinal,outcome_step depth value gap hp hv]

theorem loopFinal_zero (archive depth : List Bool) (value gap : Nat) (hp : true∈depth)
    (hv : PSTRTMIncrement009.valueDigits depth=1) :
    loopFinal archive depth value gap=PSTRTMThresholdDepthLoopZero176.zeroFinal archive depth value gap := by
  simp only [loopFinal,outcome_zero depth value gap hp hv]
  unfold PSTRTMThresholdDepthLoopZero176.zeroFinal
  rw [PSTRTMThresholdCounterReturn175.return_final_tape]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopTrace179
