module

public import B23_4_RatWordPrep_SeqCmp_RawClock_027

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.RawGetter.Public

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open Cost

/-- Normal public import, physically starts with the caller's current
bank. The only stream hypothesis identifies the original raw field at
the real cursor; it supplies no result packet, width, fuel or path. -/
theorem fixed_source (C : Type*) :
    ∃ (source : Label → Statement C) (clockA chargeA power : Nat),
      source .done=.halt ∧ 0<clockA ∧ 0<chargeA ∧ power=4 ∧
      ∀ (background : RatInput.Stack → List Bool) (memory : Store C) (x : Rat) (suffix : List Bool),
        ListBlank.mk (background 0)=ListBlank.mk (encodeDatum (.rational x)++suffix++[true]) →
        ∃ trace final parsed,Facts source background memory x suffix trace final parsed ∧
          traceClockSum source trace≤clockA*(inputScale background x)^power ∧
          chargedCost source trace≤chargeA*(inputScale background x)^power := by
  refine ⟨program .halt,clockSumCoefficient,chargedCoefficient,clockSumDegree,rfl,
    clockSumCoefficient_pos,chargedCoefficient_pos,clockSumDegree_eq_four,?_⟩
  intro background memory x suffix right
  obtain ⟨trace,final,parsed,facts⟩ := actual_polynomial_current background memory x suffix right
  exact ⟨trace,final,parsed,facts,traceClockSum_le facts,chargedCost_le facts⟩

theorem final_fields {C : Type*} {source : Label → Statement C} {background : RatInput.Stack → List Bool}
    {memory : Store C} {x : Rat} {suffix : List Bool} {trace : List (State C)} {final parsed : State C}
    (facts : Facts source background memory x suffix trace final parsed) :
    final.stk 15=RatInput.Encoder.packet x (background 15) ∧ final.stk 7=background 7 ∧
      final.stk 0=parsed.stk 0 ∧ final.stk 1=parsed.stk 1 ∧
      ∀ slot,¬Work slot→final.stk slot=background slot := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [facts.contents,Function.update_self]
  · rw [facts.contents]
    exact facts.scratch
  · rw [facts.contents]
    rfl
  · rw [facts.contents]
    rfl
  · exact (facts.boundaries final (List.mem_of_getLast? facts.last)).2.2.2

end B23_4_RatWordPrep.RawGetter.Public
