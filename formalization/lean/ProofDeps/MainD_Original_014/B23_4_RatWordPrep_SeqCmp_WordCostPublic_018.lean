module

public import B23_4_RatWordPrep_SeqCmp_WordClock_017

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp.Word.Cost.Public

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

/-- SAME full original-output witness, now with both the true sum of
primitive clocks and a conservative charged TM2 cost. Operand production
from the original input is still a separate caller obligation. -/
theorem fixed_source (C : Type*) :
    ∃ (source : Label → Statement C) (clockA chargeA power : Nat),
      source .done=.halt ∧ 0<clockA ∧ 0<chargeA ∧ power=8 ∧
      ∀ (background : RatInput.Stack → List Bool) (memory : Store C)
        (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) (tail scratch : List Bool),
        ∃ trace final,
          Facts source background memory (E.rationalWordOdds word) (p/(1-p)) ((1-p)/p) tail scratch trace final ∧
          final.stk 13=wordOutput E p word ∧
          traceClockSum source trace≤clockA*(inputScale background (E.rationalWordOdds word) (p/(1-p)) ((1-p)/p) tail scratch)^power ∧
          chargedCost source trace≤chargeA*(inputScale background (E.rationalWordOdds word) (p/(1-p)) ((1-p)/p) tail scratch)^power := by
  obtain ⟨source,done,actual⟩ := Word.Public.fixed_source C
  refine ⟨source,clockSumCoefficient,chargedCoefficient,clockSumDegree,done,
    clockSumCoefficient_pos,chargedCoefficient_pos,clockSumDegree_eq_eight,?_⟩
  intro background memory E p word tail scratch
  obtain ⟨trace,final,facts,raw,_otherStacks⟩ := actual background memory E p word tail scratch
  exact ⟨trace,final,facts,raw,traceClockSum_le facts,chargedCost_le facts⟩

end B23_4_RatWordPrep.SeqCmp.Word.Cost.Public
