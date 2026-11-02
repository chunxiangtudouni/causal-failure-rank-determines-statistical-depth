module

public import Common.PSTR_WordBool_BoolStackTrace_015
public import Common.PSTR_WordBool_StackGeometry_013
public import Common.PSTR_TM_Trace_002

/-! Ghost endpoints of the SAME actual source edge. They are identified
using deterministic step equality, not inferred from weak Tape equality. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.BoolStackEndpoints

open Turing BoolOnStacks BoolStackStep BoolStackRefines BoolStackTrace StackGeometry
open PaperProofs.Common.Native.RationalControllerComputation (displacement)

variable {states : Nat}

theorem cfg_endpoints (action : StackGeometry.Action) (position : Int) (left right afterLeft afterRight : List Bool)
    (label : Option Unit) (control : Fin (states + 1)) (scratch : Bool)
    (leftLength : afterLeft.length = leftSize action left.length)
    (rightLength : afterRight.length = rightSize action right.length) :
    position + delta action - ((cfg label control scratch afterLeft afterRight).stk 1).length =
      min (position - left.length) (position + delta action) ∧
    position + delta action + ((cfg label control scratch afterLeft afterRight).stk 0).length =
      max (position + right.length) (position + 1) := by
  change position + delta action - (afterLeft.length : Int) = _ ∧
    position + delta action + (afterRight.length : Int) = _
  rw [leftLength, rightLength]
  exact ⟨left_endpoint action position left.length, right_endpoint action position right.length⟩

theorem macro_geometry (machine : TM0.Machine Bool (Fin (states + 1)))
    (control : Fin (states + 1)) (scratch : Bool) (left right : List Bool) (position : Int) :
    ∃ after : BoolOnStacks.State states,
      TM2.step (program machine) (cfg (some ()) control scratch left right) = some after ∧
      let nextPosition := position + displacement machine
        (representedState (cfg (some ()) control scratch left right))
      nextPosition - (after.stk 1).length = min (position - left.length) nextPosition ∧
      nextPosition + (after.stk 0).length = max (position + right.length) (position + 1) := by
  cases actual : machine control (headBit right) with
  | none =>
    have shift : displacement machine (representedState (cfg (some ()) control scratch left right)) =
        delta .halt := by
      rw [represented_cfg]
      simp only [displacement, tape_head, actual, delta]
    refine ⟨cfg none control (headBit right) left (headBit right :: right.tail),
      halt_step machine control scratch left right actual, ?_⟩
    dsimp only
    rw [shift]
    apply cfg_endpoints .halt
    · rfl
    · simp only [List.length_cons, List.length_tail, rightSize]
      omega
  | some instruction =>
    obtain ⟨next, action⟩ := instruction
    cases action with
    | write value =>
      have shift : displacement machine (representedState (cfg (some ()) control scratch left right)) =
          delta .write := by
        rw [represented_cfg]
        simp only [displacement, tape_head, actual, delta]
      refine ⟨cfg (some ()) next (headBit right) left (value :: right.tail),
        write_step machine control next scratch value left right actual, ?_⟩
      dsimp only
      rw [shift]
      apply cfg_endpoints .write
      · rfl
      · simp only [List.length_cons, List.length_tail, rightSize]
        omega
    | move direction =>
      cases direction with
      | right =>
        have shift : displacement machine (representedState (cfg (some ()) control scratch left right)) =
            delta .right := by
          rw [represented_cfg]
          simp only [displacement, tape_head, actual, delta]
        refine ⟨cfg (some ()) next (headBit right) (headBit right :: left) right.tail,
          right_step machine control next scratch left right actual, ?_⟩
        dsimp only
        rw [shift]
        apply cfg_endpoints .right
        · rfl
        · exact List.length_tail
      | left =>
        have shift : displacement machine (representedState (cfg (some ()) control scratch left right)) =
            delta .left := by
          rw [represented_cfg]
          simp only [displacement, tape_head, actual, delta]
        refine ⟨cfg (some ()) next (headBit left) left.tail
          (headBit left :: headBit right :: right.tail),
          left_step machine control next scratch left right actual, ?_⟩
        dsimp only
        rw [shift]
        apply cfg_endpoints .left
        · exact List.length_tail
        · simp only [List.length_cons, List.length_tail, rightSize]
          omega

theorem edge_geometry (machine : TM0.Machine Bool (Fin (states + 1)))
    (before after : BoolOnStacks.State states) (position : Int) (active : before.l = some ())
    (edge : TM2.step (program machine) before = some after) :
    let nextPosition := position + displacement machine (representedState before)
    nextPosition - (after.stk 1).length = min (position - (before.stk 1).length) nextPosition ∧
    nextPosition + (after.stk 0).length = max (position + (before.stk 0).length) (position + 1) := by
  have canonical := reconstruct before active
  obtain ⟨chosen, actual, geometry⟩ := macro_geometry machine before.var.1 before.var.2
    (before.stk 1) (before.stk 0) position
  rw [canonical] at actual geometry
  have same : chosen = after := Option.some.inj (actual.symm.trans edge)
  subst chosen
  exact geometry

end PaperProofs.Common.Native.PSTRWordBool.BoolStackEndpoints
