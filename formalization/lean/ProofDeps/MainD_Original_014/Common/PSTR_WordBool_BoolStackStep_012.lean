module

public import Common.PSTR_WordBool_BoolOnStacks_011

/-! Actual source macro transitions, including a charged source HALT.
The scratch bit at macro entry is unconstrained. Blank tapes are compared
as ListBlank values; an explicit stored FALSE is not an empty stack. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.BoolStackStep

open Turing BoolOnStacks

variable {states : Nat}

def headBit (word : List Bool) : Bool := word.head?.getD false

def cfg (label : Option Unit) (control : Fin (states + 1)) (scratch : Bool)
    (left right : List Bool) : State states :=
  ⟨label, (control, scratch), PushPop.stackContents right left⟩

theorem slot_zero (right left : List Bool) : PushPop.stackContents right left 0 = right := rfl
theorem slot_one (right left : List Bool) : PushPop.stackContents right left 1 = left := rfl

theorem update_right (right left replacement : List Bool) :
    Function.update (PushPop.stackContents right left) 0 replacement =
      PushPop.stackContents replacement left := by
  funext slot
  fin_cases slot <;> simp [PushPop.stackContents]

theorem update_left (right left replacement : List Bool) :
    Function.update (PushPop.stackContents right left) 1 replacement =
      PushPop.stackContents right replacement := PushPop.update_scratch right left replacement

theorem halt_step (machine : TM0.Machine Bool (Fin (states + 1)))
    (control : Fin (states + 1)) (scratch : Bool) (left right : List Bool)
    (actual : machine control (headBit right) = none) :
    TM2.step (program machine) (cfg (some ()) control scratch left right) =
      some (cfg none control (headBit right) left (headBit right :: right.tail)) := by
  dsimp only [headBit] at actual ⊢
  simp [cfg, program, TM2.step, TM2.stepAux, capture, slot_zero, update_right, actual]

theorem write_step (machine : TM0.Machine Bool (Fin (states + 1)))
    (control next : Fin (states + 1)) (scratch value : Bool) (left right : List Bool)
    (actual : machine control (headBit right) = some (next, .write value)) :
    TM2.step (program machine) (cfg (some ()) control scratch left right) =
      some (cfg (some ()) next (headBit right) left (value :: right.tail)) := by
  dsimp only [headBit] at actual ⊢
  simp [cfg, program, TM2.step, TM2.stepAux, capture, slot_zero, update_right,
    isWrite, written, updateControl, actual]

theorem right_step (machine : TM0.Machine Bool (Fin (states + 1)))
    (control next : Fin (states + 1)) (scratch : Bool) (left right : List Bool)
    (actual : machine control (headBit right) = some (next, .move .right)) :
    TM2.step (program machine) (cfg (some ()) control scratch left right) =
      some (cfg (some ()) next (headBit right) (headBit right :: left) right.tail) := by
  dsimp only [headBit] at actual ⊢
  simp [cfg, program, TM2.step, TM2.stepAux, capture, slot_zero, slot_one,
    update_right, update_left, isWrite, isRight, updateControl, actual]

theorem left_step (machine : TM0.Machine Bool (Fin (states + 1)))
    (control next : Fin (states + 1)) (scratch : Bool) (left right : List Bool)
    (actual : machine control (headBit right) = some (next, .move .left)) :
    TM2.step (program machine) (cfg (some ()) control scratch left right) =
      some (cfg (some ()) next (headBit left) left.tail
        (headBit left :: headBit right :: right.tail)) := by
  dsimp only [headBit] at actual ⊢
  simp [cfg, program, TM2.step, TM2.stepAux, capture, slot_zero, slot_one,
    update_right, update_left, isWrite, isRight, updateControl, actual]

theorem blank_head (word : List Bool) : (ListBlank.mk word).head = headBit word := by
  cases word <;> rfl

theorem restore_blank (word : List Bool) :
    ListBlank.mk (headBit word :: word.tail) = ListBlank.mk word := by
  calc
    ListBlank.mk (headBit word :: word.tail) =
        (ListBlank.mk word).tail.cons (ListBlank.mk word).head := by
      rw [ListBlank.tail_mk, blank_head, ListBlank.cons_mk]
    _ = ListBlank.mk word := ListBlank.cons_head_tail _

theorem restored_tape (left right : List Bool) :
    Tape.mk₂ left (headBit right :: right.tail) = Tape.mk₂ left right := by
  unfold Tape.mk₂
  rw [restore_blank]

theorem write_tape (left right : List Bool) (value : Bool) :
    Tape.mk₂ left (value :: right.tail) = (Tape.mk₂ left right).write value := by
  unfold Tape.mk₂
  rw [Tape.write_mk', ListBlank.tail_mk, ListBlank.cons_mk]

theorem right_tape (left right : List Bool) :
    Tape.mk₂ (headBit right :: left) right.tail = (Tape.mk₂ left right).move .right := by
  unfold Tape.mk₂
  rw [Tape.move_right_mk', blank_head, ListBlank.cons_mk, ListBlank.tail_mk]

theorem left_tape (left right : List Bool) :
    Tape.mk₂ left.tail (headBit left :: headBit right :: right.tail) =
      (Tape.mk₂ left right).move .left := by
  unfold Tape.mk₂
  rw [Tape.move_left_mk', blank_head, ListBlank.tail_mk, ListBlank.cons_mk]
  rw [← ListBlank.cons_mk, restore_blank, ListBlank.cons_mk]

end PaperProofs.Common.Native.PSTRWordBool.BoolStackStep
