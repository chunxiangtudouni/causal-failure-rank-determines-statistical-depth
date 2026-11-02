module

public import Common.PSTR_WordBool_IsolatedRatSub_073
public import Common.PSTR_SYM_RatExportRun_094

/-! Actual original singleton-Rat output reader. It pays for every finite
work cell, count1/tag/sign, both real Nat headers/payloads and TRUE footer.
Target is the EXISTING094 packet. Old7/15 are arbitrary carried tails. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatOutput

open Turing
open RationalControllerComputation PA17TMRatArithmeticParse002 PSTRTMRawNat010

abbrev Stack := Fin 16
abbrev Label := Fin 9
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Bool × Bool
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (C × Store)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (C × Store)

variable {C : Type*}

def capture (memory : C × Store) (value : Option Bool) : C × Store :=
  (memory.1, (value.isSome, value.getD false))
def keep (memory : C × Store) (_value : Option Bool) : C × Store := memory
def bit (memory : C × Store) : Bool := memory.2.2
def present (memory : C × Store) : Bool := memory.2.1
def jump (point : Label) : Statement C := .goto (fun _ => point)

def program (caller : Statement C) (point : Label) : Statement C :=
  match point.val with
  | 0 => .pop 14 capture (.branch present (jump 0) (jump 1))
  | 1 => .pop 13 keep (.pop 13 keep (.pop 13 keep (.pop 13 keep
      (.pop 13 capture (.push 14 (fun _ => true) (.push 14 bit
        (.push 7 (fun _ => true) (jump 2))))))))
  | 2 => .pop 13 capture (.branch bit (.push 7 (fun _ => false) (jump 2)) (jump 3))
  | 3 => .pop 7 capture (.branch bit
      (.push 14 (fun _ => false) (.push 14 (fun _ => false) (.push 7 (fun _ => true) (jump 4))))
      (.pop 13 capture (.push 14 (fun _ => true) (.push 14 bit (jump 3)))))
  | 4 => .pop 13 capture (.branch bit (.push 7 (fun _ => false) (jump 4)) (jump 5))
  | 5 => .pop 7 capture (.branch bit
      (.push 14 (fun _ => false) (.push 14 (fun _ => false) (.pop 13 keep (jump 6))))
      (.pop 13 capture (.push 14 (fun _ => true) (.push 14 bit (jump 5)))))
  | 6 => .pop 13 capture (.branch present (jump 6) (jump 7))
  | 7 => .pop 14 capture (.branch present (.push 15 bit (jump 7)) (jump 8))
  | _ => caller

def cells (background : Stack → List Bool) (right left counter target : List Bool) : Stack → List Bool :=
  fun point => if point = 13 then right else if point = 14 then left else if point = 7 then counter
    else if point = 15 then target else background point

def state (background : Stack → List Bool) (point : Label) (context : C) (memory : Store)
    (right left counter target : List Bool) : State C :=
  ⟨some point, (context,memory), cells background right left counter target⟩

theorem right_at (background : Stack → List Bool) (right left counter target : List Bool) :
    cells background right left counter target 13 = right := rfl
theorem left_at (background : Stack → List Bool) (right left counter target : List Bool) :
    cells background right left counter target 14 = left := rfl
theorem counter_at (background : Stack → List Bool) (right left counter target : List Bool) :
    cells background right left counter target 7 = counter := rfl
theorem target_at (background : Stack → List Bool) (right left counter target : List Bool) :
    cells background right left counter target 15 = target := rfl

theorem update_right (background : Stack → List Bool) (right left counter target next : List Bool) :
    Function.update (cells background right left counter target) 13 next = cells background next left counter target := by
  funext point; fin_cases point <;> rfl
theorem update_left (background : Stack → List Bool) (right left counter target next : List Bool) :
    Function.update (cells background right left counter target) 14 next = cells background right next counter target := by
  funext point; fin_cases point <;> rfl
theorem update_counter (background : Stack → List Bool) (right left counter target next : List Bool) :
    Function.update (cells background right left counter target) 7 next = cells background right left next target := by
  funext point; fin_cases point <;> rfl
theorem update_target (background : Stack → List Bool) (right left counter target next : List Bool) :
    Function.update (cells background right left counter target) 15 next = cells background right left counter next := by
  funext point; fin_cases point <;> rfl

def outside (background : Stack → List Bool) : Nat :=
  ∑ point, if point = (13 : Stack) ∨ point = 14 ∨ point = 7 ∨ point = 15 then 0 else (background point).length

def occupied (contents : Stack → List Bool) : Nat := ∑ point, (contents point).length

theorem occupied_state (background : Stack → List Bool) (point : Label) (context : C) (memory : Store)
    (right left counter target : List Bool) :
    occupied (state background point context memory right left counter target).stk =
      outside background + right.length + left.length + counter.length + target.length := by
  simp [occupied, outside, state, cells, Fin.sum_univ_succ, Nat.add_assoc]
  omega

theorem clear_left_step (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (cell : Bool) (right left counter target : List Bool) :
    TM2.step (program caller) (state background 0 context memory right (cell::left) counter target) =
      some (state background 0 context (true,cell) right left counter target) := by
  simp [state, TM2.step, program, TM2.stepAux, left_at, capture, present, jump, update_left]

theorem clear_left_done (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (right counter target : List Bool) :
    TM2.step (program caller) (state background 0 context memory right [] counter target) =
      some (state background 1 context (false,false) right [] counter target) := by
  simp [state, TM2.step, program, TM2.stepAux, left_at, capture, present, jump, update_left]

theorem start_step (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (negative : Bool) (right left counter target : List Bool) :
    TM2.step (program caller) (state background 1 context memory
      (true::false::true::true::negative::right) left counter target) =
      some (state background 2 context (true,negative) right (negative::true::left) (true::counter) target) := by
  simp [state, TM2.step, program, TM2.stepAux, right_at, left_at, counter_at,
    keep, capture, bit, jump, update_right, update_left, update_counter]

theorem header_true (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (second : Bool) (right left counter target : List Bool) :
    TM2.step (program caller) (state background (if second then 4 else 2) context memory
      (true::right) left counter target) =
      some (state background (if second then 4 else 2) context (true,true) right left (false::counter) target) := by
  cases second <;> simp [state, TM2.step, program, TM2.stepAux, right_at, counter_at, capture,
    bit, jump, update_right, update_counter]

theorem header_false (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (second : Bool) (right left counter target : List Bool) :
    TM2.step (program caller) (state background (if second then 4 else 2) context memory
      (false::right) left counter target) =
      some (state background (if second then 5 else 3) context (true,false) right left counter target) := by
  cases second <;> simp [state, TM2.step, program, TM2.stepAux, right_at, capture, bit, jump, update_right]

theorem payload_step (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (second digit : Bool) (right left counter target : List Bool) :
    TM2.step (program caller) (state background (if second then 5 else 3) context memory
      (digit::right) left (false::counter) target) =
      some (state background (if second then 5 else 3) context (true,digit) right
        (digit::true::left) counter target) := by
  cases second <;> simp [state, TM2.step, program, TM2.stepAux, right_at, left_at, counter_at,
    capture, bit, jump, update_right, update_left, update_counter]

theorem numerator_done (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (right left counter target : List Bool) :
    TM2.step (program caller) (state background 3 context memory right left (true::counter) target) =
      some (state background 4 context (true,true) right (false::false::left) (true::counter) target) := by
  simp [state, TM2.step, program, TM2.stepAux, left_at, counter_at, capture, bit, jump, update_left, update_counter]

theorem denominator_done (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (right left counter target : List Bool) :
    TM2.step (program caller) (state background 5 context memory right left (true::counter) target) =
      some (state background 6 context (true,true) right.tail (false::false::left) counter target) := by
  simp [state, TM2.step, program, TM2.stepAux, right_at, left_at, counter_at, capture, bit, keep,
    jump, update_right, update_left, update_counter]

theorem clear_right_step (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (cell : Bool) (right left counter target : List Bool) :
    TM2.step (program caller) (state background 6 context memory (cell::right) left counter target) =
      some (state background 6 context (true,cell) right left counter target) := by
  simp [state, TM2.step, program, TM2.stepAux, right_at, capture, present, jump, update_right]

theorem clear_right_done (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (left counter target : List Bool) :
    TM2.step (program caller) (state background 6 context memory [] left counter target) =
      some (state background 7 context (false,false) [] left counter target) := by
  simp [state, TM2.step, program, TM2.stepAux, right_at, capture, present, jump, update_right]

theorem reverse_step (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (cell : Bool) (right left counter target : List Bool) :
    TM2.step (program caller) (state background 7 context memory right (cell::left) counter target) =
      some (state background 7 context (true,cell) right left counter (cell::target)) := by
  simp [state, TM2.step, program, TM2.stepAux, left_at, target_at, capture, present, bit, jump, update_left, update_target]

theorem reverse_done (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (right counter target : List Bool) :
    TM2.step (program caller) (state background 7 context memory right [] counter target) =
      some (state background 8 context (false,false) right [] counter target) := by
  simp [state, TM2.step, program, TM2.stepAux, left_at, capture, present, jump, update_left]

end PaperProofs.Common.Native.PSTRWordBool.RatOutput
