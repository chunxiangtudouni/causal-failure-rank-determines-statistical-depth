module

public import B23_4_RatWordPrep_SeqCmp_WordPlanScale_148
public import B23_4_RatWordPrep_SeqCmp_WordSerializeResources_151
public import B23_4_RatWordPrep_SeqCmp_WordHaltResources_152

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

def tailCoefficient : Nat := 10000*(planCoefficient+81*SeqCmp.Word.coefficient+1)
def tailBudget (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  tailCoefficient*(planScale frame E target word)^4

theorem planBudget_le_tail (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    planBudget frame E target word≤tailBudget frame E target word :=
  Nat.mul_le_mul_right _ (by unfold tailCoefficient; omega)

theorem original_pairs_quadratic (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    RatPair.fieldSize (E.rationalWordOdds word) (target/(1-target))≤8*((wordInput E target word).length+1)^2 ∧
    RatPair.fieldSize ((1-target)/target) (E.rationalWordOdds word)≤8*((wordInput E target word).length+1)^2 ∧
    RatPair.fieldSize 1 (E.rationalWordOdds word)≤8*((wordInput E target word).length+1)^2 ∧
    RatInput.Encoder.fieldSize (E.rationalWordOdds word)≤8*((wordInput E target word).length+1)^2 := by
  have original := RootB23.WordOddsBits.original_pair_bounds E target word
  have count := word_length_le_input E target word
  have widthCap : RootB23.WordOddsBits.prefixBound E target word word.1≤8*((wordInput E target word).length+1)^2 := by
    unfold RootB23.WordOddsBits.prefixBound
    calc
      _≤8*((wordInput E target word).length+1)*((wordInput E target word).length+1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 (Nat.add_le_add_right count 1))
      _=8*((wordInput E target word).length+1)^2 := by ring
  exact ⟨original.1.trans widthCap,original.2.1.trans widthCap,original.2.2.1.trans widthCap,original.2.2.2.trans widthCap⟩

theorem word_scale_le_plan (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (data : Data) (capacity : PlanData E target word data) (before : State C) (shape : before.stk=layout frame data) :
    SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7)≤
      3*planScale frame E target word := by
  have actual := capacity.scale_bound frame before shape
  have fields := original_pairs_quadratic E target word
  have outside := pair_outside_le_mass before.stk
  have scratch := RatInput.Encoder.point_mass before.stk 7
  have room : 4*(8*((wordInput E target word).length+1)^2)≤planScale frame E target word := by unfold planScale; omega
  unfold SeqCmp.Word.inputScale
  simp only [List.length_nil]
  unfold scale at actual
  omega

theorem word_budget_le_plan (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (data : Data) (capacity : PlanData E target word data) (before : State C) (shape : before.stk=layout frame data) :
    SeqCmp.Word.coefficient*(SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7))^SeqCmp.Word.degree≤
      (81*SeqCmp.Word.coefficient)*(planScale frame E target word)^4 := by
  have powered := Nat.pow_le_pow_left (word_scale_le_plan frame E target word data capacity before shape) 4
  rw [SeqCmp.Word.degree]
  exact (Nat.mul_le_mul_left SeqCmp.Word.coefficient powered).trans_eq (by ring)

theorem word_tail_bounds {caller : Statement C} {before final : State C} {run : Segment caller before final}
    (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (data : Data) (capacity : PlanData E target word data) (shape : before.stk=layout frame data)
    (bounds : RunBounds caller run
      (SeqCmp.Word.coefficient*(SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7))^SeqCmp.Word.degree)
      (SeqCmp.Word.coefficient*(SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7))^SeqCmp.Word.degree)
      (SeqCmp.Word.coefficient*(SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7))^SeqCmp.Word.degree)) :
    RunBounds caller run (tailBudget frame E target word) (tailBudget frame E target word) (tailBudget frame E target word) := by
  have constant : 81*SeqCmp.Word.coefficient≤tailCoefficient := by unfold tailCoefficient; omega
  have cap := (word_budget_le_plan frame E target word data capacity before shape).trans (Nat.mul_le_mul_right _ constant)
  exact bounds.mono cap cap cap

/-- The finalizer is linear in the actual serialized entry mass. A
single conservative WordStage boundary bound suffices here; no repeated
native quartic envelope is introduced. -/
theorem halt_tail_bounds {caller : Statement C} {before middle final : State C}
    {wordRun : Segment caller before middle} {haltRun : Segment caller middle final}
    (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (data : Data) (capacity : PlanData E target word data) (shape : before.stk=layout frame data)
    (wordBounds : RunBounds caller wordRun
      (SeqCmp.Word.coefficient*(SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7))^SeqCmp.Word.degree)
      (SeqCmp.Word.coefficient*(SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7))^SeqCmp.Word.degree)
      (SeqCmp.Word.coefficient*(SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7))^SeqCmp.Word.degree))
    (haltBounds : RunBounds caller haltRun (12*scale middle) (18*scale middle) (84*scale middle)) :
    RunBounds caller haltRun (tailBudget frame E target word) (tailBudget frame E target word) (tailBudget frame E target word) := by
  have mass := wordBounds.boundary_mass middle (List.mem_of_getLast? wordRun.last)
  have cap := word_budget_le_plan frame E target word data capacity before shape
  have positive := planScale_pos frame E target word
  have one : 1≤(planScale frame E target word)^4 := positive.trans (SeqCmp.linear_fourth _ positive)
  have scaled : scale middle≤(16*81*SeqCmp.Word.coefficient+1)*(planScale frame E target word)^4 := by
    unfold scale
    nlinarith
  have constant : 84*(16*81*SeqCmp.Word.coefficient+1)≤tailCoefficient := by unfold tailCoefficient; omega
  have clock : 84*scale middle≤tailBudget frame E target word := by
    calc
      _≤84*((16*81*SeqCmp.Word.coefficient+1)*(planScale frame E target word)^4) := Nat.mul_le_mul_left 84 scaled
      _=(84*(16*81*SeqCmp.Word.coefficient+1))*(planScale frame E target word)^4 := by ring
      _≤tailCoefficient*(planScale frame E target word)^4 := Nat.mul_le_mul_right _ constant
  exact haltBounds.mono ((Nat.mul_le_mul_right _ (by decide : 12≤84)).trans clock)
    ((Nat.mul_le_mul_right _ (by decide : 18≤84)).trans clock) clock

end B23_4_RatWordPrep.WordFinish.Resources
