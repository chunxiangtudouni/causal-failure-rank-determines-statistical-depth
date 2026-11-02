module
public import Structure.PA17_TM_RatArithmetic_RatDivController_070b

/-! Unqualified original-codec division computation and fixed-program
existence, with every visited-space prefix on the same actual run. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivController070

open Turing

theorem original_div_computes (x y : Rat) :
    computes divMachine (encode [.rational x,.rational y]) (encode [.rational (x/y)])
      (divResourceCoefficient*originalPower x y) (divResourceCoefficient*originalPower x y) := by
  obtain ⟨trace,final,actual,whole,time,space⟩ := original_div_contract x y
  refine ⟨trace,final,actual,?_,time,?_⟩
  · rw [whole]
    exact Turing.Tape.mk'_right₀ _ _
  · have h := space trace.length
    simpa only [List.take_length] using h

/-- Finite code and positive c,d precede every original rational input.
There is no denominator, zero, room, sign, width, count or fuel qualification. -/
theorem original_div_exists :
    ∃ states c d : Nat, ∃ program : Machine states, 0<c ∧ 0<d ∧
      ∀ x y : Rat, ∃ trace final,
        Runs program (encode [.rational x,.rational y]) trace final ∧
        final.Tape=Tape.mk₁ (encode [.rational (x/y)]) ∧
        trace.length≤c*((encode [.rational x,.rational y]).length+1)^d ∧
        ∀ prefixLength, visitedSpace program (encode [.rational x,.rational y]).length
          (trace.take prefixLength)≤c*((encode [.rational x,.rational y]).length+1)^d := by
  refine ⟨controllerCap,divResourceCoefficient,4,divMachine,divResourceCoefficient_pos,by decide,?_⟩
  intro x y
  exact original_div_contract x y

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivController070
