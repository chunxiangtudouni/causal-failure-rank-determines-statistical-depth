module

public import Common.PSTR_WordBool_WordNatCaller_046
public import Init.Data.BitVec.Lemmas

/-! Future007 SOURCEONLY. Fixed actual canonical-Nat result reader. The
virtual native callee may leave explicit FALSE work cells; its output is a
ListBlank/tape contract, not an exact finite-stack suffix. Clear real L first,
read the actual unary header, consume all payload bits, retain only the first
w, physically pad to w, restore width, clear real R, and pay the return.
No native result or canonical tail is fabricated by this source. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordNatIO

open PaperProofs.Common.Native.RationalControllerComputation

theorem valueDigits_ofBoolListLE (digits : List Bool) :
    PSTRTMIncrement009.valueDigits digits = (BitVec.ofBoolListLE digits).toNat := by
  apply Nat.eq_of_testBit_eq
  intro point
  rw [PSTRTMNatValue017.testBit_valueDigits, BitVec.testBit_toNat,
    BitVec.getLsbD_ofBoolListLE]
  exact (List.getD_default_eq_getI (l := digits) (n := point)).symm

end PaperProofs.Common.Native.PSTRWordBool.WordNatIO

namespace PaperProofs.Common.Native.PSTRWordBool.NatWordIO

open Turing

abbrev Stack := Fin 16
abbrev Label := Fin 8
abbrev Store := Bool × Bool
abbrev Alphabet (_ : Stack) := Bool
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def capture (_memory : Store) (value : Option Bool) : Store :=
  (value.isSome, value.getD false)

def presence (memory : Store) (value : Option Bool) : Store := (value.isSome, memory.2)

def jump (label : Label) : Statement := .goto (fun _ => label)

def program (caller : Statement) (label : Label) : Statement :=
  match label.val with
  | 0 => .pop 1 capture (.branch Prod.fst (jump 0) (jump 1))
  | 1 => .pop 0 capture (.branch Prod.snd (.push 1 (fun _ => true) (jump 1)) (jump 2))
  | 2 => .pop 1 capture (.branch Prod.fst
      (.pop 0 capture (.pop 11 presence (.branch Prod.fst
        (.push 7 Prod.snd (.push 12 (fun _ => true) (jump 2))) (jump 2)))) (jump 3))
  | 3 => .pop 11 capture (.branch Prod.fst
      (.push 7 (fun _ => false) (.push 12 (fun _ => true) (jump 3))) (jump 4))
  | 4 => .pop 7 capture (.branch Prod.fst
      (.pop 12 (fun memory _ => memory)
        (.push 11 (fun _ => true) (.push 3 Prod.snd (jump 4)))) (jump 5))
  | 5 => .pop 0 capture (.branch Prod.fst (jump 5) (jump 6))
  | 6 => jump 7
  | _ => caller

theorem program_zero (caller : Statement) : program caller 0 =
    .pop 1 capture (.branch Prod.fst (jump 0) (jump 1)) := rfl

theorem program_one (caller : Statement) : program caller 1 =
    .pop 0 capture (.branch Prod.snd (.push 1 (fun _ => true) (jump 1)) (jump 2)) := rfl

theorem program_two (caller : Statement) : program caller 2 =
    .pop 1 capture (.branch Prod.fst
      (.pop 0 capture (.pop 11 presence (.branch Prod.fst
        (.push 7 Prod.snd (.push 12 (fun _ => true) (jump 2))) (jump 2)))) (jump 3)) := rfl

theorem program_three (caller : Statement) : program caller 3 =
    .pop 11 capture (.branch Prod.fst
      (.push 7 (fun _ => false) (.push 12 (fun _ => true) (jump 3))) (jump 4)) := rfl

theorem program_four (caller : Statement) : program caller 4 =
    .pop 7 capture (.branch Prod.fst
      (.pop 12 (fun memory _ => memory)
        (.push 11 (fun _ => true) (.push 3 Prod.snd (jump 4)))) (jump 5)) := rfl

theorem program_five (caller : Statement) : program caller 5 =
    .pop 0 capture (.branch Prod.fst (jump 5) (jump 6)) := rfl

theorem program_six (caller : Statement) : program caller 6 = jump 7 := rfl

def cells (background : Stack → List Bool)
    (right left value reverseWord width used : List Bool) (slot : Stack) : List Bool :=
  if slot = 0 then right else if slot = 1 then left else if slot = 3 then value else
    if slot = 7 then reverseWord else if slot = 11 then width else if slot = 12 then used else background slot

def state (background : Stack → List Bool) (label : Label) (memory : Store)
    (right left value reverseWord width used : List Bool) : State :=
  ⟨some label, memory, cells background right left value reverseWord width used⟩

theorem cells_right (background : Stack → List Bool) (right left value reverseWord width used : List Bool) :
    cells background right left value reverseWord width used 0 = right := rfl

theorem cells_left (background : Stack → List Bool) (right left value reverseWord width used : List Bool) :
    cells background right left value reverseWord width used 1 = left := rfl

theorem cells_value (background : Stack → List Bool) (right left value reverseWord width used : List Bool) :
    cells background right left value reverseWord width used 3 = value := rfl

theorem cells_reverse (background : Stack → List Bool) (right left value reverseWord width used : List Bool) :
    cells background right left value reverseWord width used 7 = reverseWord := rfl

theorem cells_width (background : Stack → List Bool) (right left value reverseWord width used : List Bool) :
    cells background right left value reverseWord width used 11 = width := rfl

theorem cells_used (background : Stack → List Bool) (right left value reverseWord width used : List Bool) :
    cells background right left value reverseWord width used 12 = used := rfl

theorem cells_frame (background : Stack → List Bool) (right left value reverseWord width used : List Bool)
    (slot : Stack) (notRight : slot ≠ 0) (notLeft : slot ≠ 1) (notValue : slot ≠ 3)
    (notReverse : slot ≠ 7) (notWidth : slot ≠ 11) (notUsed : slot ≠ 12) :
    cells background right left value reverseWord width used slot = background slot := by
  simp only [cells, ite_eq_right notRight, ite_eq_right notLeft, ite_eq_right notValue,
    ite_eq_right notReverse, ite_eq_right notWidth, ite_eq_right notUsed]

theorem update_right (background : Stack → List Bool)
    (right left value reverseWord width used replacement : List Bool) :
    Function.update (cells background right left value reverseWord width used) 0 replacement =
      cells background replacement left value reverseWord width used := by
  funext slot
  fin_cases slot <;> simp [cells, Function.update]

theorem update_left (background : Stack → List Bool)
    (right left value reverseWord width used replacement : List Bool) :
    Function.update (cells background right left value reverseWord width used) 1 replacement =
      cells background right replacement value reverseWord width used := by
  funext slot
  fin_cases slot <;> simp [cells, Function.update]

theorem update_value (background : Stack → List Bool)
    (right left value reverseWord width used replacement : List Bool) :
    Function.update (cells background right left value reverseWord width used) 3 replacement =
      cells background right left replacement reverseWord width used := by
  funext slot
  fin_cases slot <;> simp [cells, Function.update]

theorem update_reverse (background : Stack → List Bool)
    (right left value reverseWord width used replacement : List Bool) :
    Function.update (cells background right left value reverseWord width used) 7 replacement =
      cells background right left value replacement width used := by
  funext slot
  fin_cases slot <;> simp [cells, Function.update]

theorem update_width (background : Stack → List Bool)
    (right left value reverseWord width used replacement : List Bool) :
    Function.update (cells background right left value reverseWord width used) 11 replacement =
      cells background right left value reverseWord replacement used := by
  funext slot
  fin_cases slot <;> simp [cells, Function.update]

theorem update_used (background : Stack → List Bool)
    (right left value reverseWord width used replacement : List Bool) :
    Function.update (cells background right left value reverseWord width used) 12 replacement =
      cells background right left value reverseWord width replacement := by
  funext slot
  fin_cases slot <;> simp [cells, Function.update]

theorem clear_left_bit (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (bit : Bool) (right left value reverseWord width used : List Bool) :
    TM2.step (program caller) (state background 0 memory right (bit :: left) value reverseWord width used) =
      some (state background 0 (true, bit) right left value reverseWord width used) := by
  change some (TM2.stepAux (program caller 0) memory
    (cells background right (bit :: left) value reverseWord width used)) = _
  simp only [program_zero, TM2.stepAux, cells_left, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, jump]
  rw [update_left]
  rfl

theorem clear_left_done (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    TM2.step (program caller) (state background 0 memory right [] value reverseWord width used) =
      some (state background 1 (false, false) right [] value reverseWord width used) := by
  change some (TM2.stepAux (program caller 0) memory
    (cells background right [] value reverseWord width used)) = _
  simp only [program_zero, TM2.stepAux, cells_left, List.head?_nil, List.tail_nil, capture,
    Option.isSome_none, Option.getD_none, Bool.cond_false, jump]
  rw [update_left]
  rfl

theorem header_true (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool) :
    TM2.step (program caller) (state background 1 memory (true :: right) left value reverseWord width used) =
      some (state background 1 (true, true) right (true :: left) value reverseWord width used) := by
  change some (TM2.stepAux (program caller 1) memory
    (cells background (true :: right) left value reverseWord width used)) = _
  simp only [program_one, TM2.stepAux, cells_right, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, jump]
  rw [update_right, cells_left, update_left]
  rfl

end PaperProofs.Common.Native.PSTRWordBool.NatWordIO
