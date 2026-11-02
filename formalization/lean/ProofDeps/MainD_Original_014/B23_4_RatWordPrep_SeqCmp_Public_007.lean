module

public import B23_4_RatWordPrep_SeqCmp_Scale_006

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp.Public

open Turing
open PaperProofs.Common.Native.PSTRWordBool

/-- Ordinary public import. One source is fixed before all operand,
old-stack and finite-store inputs. No bit, trace or running-time premise. -/
theorem fixed_source (C : Type*) :
    ∃ source : Label → Statement C, source .done=.halt ∧
      ∀ (background : RatInput.Stack → List Bool) (memory : Store C)
        (a b c d : Rat) (tail scratch : List Bool),
        ∃ trace final, Facts source background memory a b c d tail scratch trace final := by
  exact ⟨program .halt,rfl,actual_polynomial⟩

example : 0<coefficient := coefficient_pos
example : degree=4 := degree_eq_four

end B23_4_RatWordPrep.SeqCmp.Public
