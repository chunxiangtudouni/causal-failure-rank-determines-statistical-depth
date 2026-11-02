module

public import RootB234_ECost_Original005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.ECost.Public

open PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation RootB234.PrepExponent

/-- Ordinary pure-cost endpoint; the existing resource wrapper consumes
this inequality on its already-chosen actual Global execution path. -/
theorem fixed_cost :
    ∃ c d : Nat, 0 < c ∧ 0 < d ∧ ∀ (background : Bank) (tail : List Bool) (budget : Rat) (number : Nat),
      Global.totalCost background tail budget number ≤ c*(Global.resourceScale background tail budget number)^d := by
  exact ⟨totalCoefficient,5,totalCoefficient_pos,by decide,fun background tail budget number =>
    total_cost background tail budget number⟩

/-- The four premises remain internal caller resource obligations.
The original computed exponent is removed by the frozen scalar theorem. -/
theorem original_cost (coefficient degree : Nat) :
    ∃ c d : Nat, 0 < c ∧ 0 < d ∧
      ∀ (I : Instance) (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
        (background : Bank) (tail : List Bool),
        RatInput.occupied background ≤ coefficient*(arithmeticScale input contract budget)^degree →
        tail.length ≤ coefficient*(arithmeticScale input contract budget)^degree →
        field budget ≤ coefficient*(arithmeticScale input contract budget)^degree →
        I.stageCount ≤ coefficient*(arithmeticScale input contract budget)^degree →
        Global.totalCost background tail budget I.stageCount ≤ c*(arithmeticScale input contract budget)^d :=
  original_scale_consumer coefficient degree

end RootB234.ECost.Public
