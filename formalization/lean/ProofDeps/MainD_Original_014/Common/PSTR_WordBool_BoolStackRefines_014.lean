module

public import Common.PSTR_WordBool_BoolStackStep_012

/-! One actual finite-store two-stack macro simulates an old Bool step.
An old terminal configuration executes an additional real source HALT.
This is semantic refinement, not yet a complete trace/workspace theorem. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.BoolStackRefines

open Turing BoolOnStacks BoolStackStep

variable {states : Nat}

theorem represented_cfg (label : Option Unit) (control : Fin (states + 1))
    (scratch : Bool) (left right : List Bool) :
    representedState (cfg label control scratch left right) = ⟨control, Tape.mk₂ left right⟩ := rfl

theorem tape_head (left right : List Bool) : (Tape.mk₂ left right).head = headBit right :=
  blank_head right

theorem macro_refines (machine : TM0.Machine Bool (Fin (states + 1)))
    (control : Fin (states + 1)) (scratch : Bool) (left right : List Bool) :
    ∃ after : State states,
      TM2.step (program machine) (cfg (some ()) control scratch left right) = some after ∧
      ((TM0.step machine (representedState (cfg (some ()) control scratch left right)) = none ∧
        after.l = none ∧ representedState after =
          representedState (cfg (some ()) control scratch left right)) ∨
        ∃ oldAfter,
          TM0.step machine (representedState (cfg (some ()) control scratch left right)) = some oldAfter ∧
          after.l = some () ∧ representedState after = oldAfter) := by
  cases actual : machine control (headBit right) with
  | none =>
    refine ⟨cfg none control (headBit right) left (headBit right :: right.tail),
      halt_step machine control scratch left right actual, Or.inl ?_⟩
    refine ⟨?_, rfl, ?_⟩
    · rw [represented_cfg]
      simp only [TM0.step, tape_head, actual, Option.map_none]
    · rw [represented_cfg, represented_cfg, restored_tape]
  | some instruction =>
    obtain ⟨next, action⟩ := instruction
    cases action with
    | write value =>
      refine ⟨cfg (some ()) next (headBit right) left (value :: right.tail),
        write_step machine control next scratch value left right actual, Or.inr ?_⟩
      refine ⟨⟨next, (Tape.mk₂ left right).write value⟩, ?_, rfl, ?_⟩
      · rw [represented_cfg]
        simp only [TM0.step, tape_head, actual, Option.map_some]
      · rw [represented_cfg, write_tape]
    | move direction =>
      cases direction with
      | right =>
        refine ⟨cfg (some ()) next (headBit right) (headBit right :: left) right.tail,
          right_step machine control next scratch left right actual, Or.inr ?_⟩
        refine ⟨⟨next, (Tape.mk₂ left right).move .right⟩, ?_, rfl, ?_⟩
        · rw [represented_cfg]
          simp only [TM0.step, tape_head, actual, Option.map_some]
        · rw [represented_cfg, right_tape]
      | left =>
        refine ⟨cfg (some ()) next (headBit left) left.tail
          (headBit left :: headBit right :: right.tail),
          left_step machine control next scratch left right actual, Or.inr ?_⟩
        refine ⟨⟨next, (Tape.mk₂ left right).move .left⟩, ?_, rfl, ?_⟩
        · rw [represented_cfg]
          simp only [TM0.step, tape_head, actual, Option.map_some]
        · rw [represented_cfg, left_tape]

end PaperProofs.Common.Native.PSTRWordBool.BoolStackRefines
