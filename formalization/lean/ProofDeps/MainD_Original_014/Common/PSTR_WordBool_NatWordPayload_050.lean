module

public import Common.PSTR_WordBool_NatWordHeader_049
public import Mathlib.Data.List.OfFn

/-! Real payload-copy/discard, physical zero padding, width restoration and
cleanup instructions of the fixed result reader. The list descriptions below
are specifications of real reads, not free copies or machine inputs. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.NatWordIO

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

def readBits (count : Nat) (right : List Bool) : List Bool :=
  List.ofFn (fun point : Fin count => right.getD point.val false)

theorem readBits_length (count : Nat) (right : List Bool) : (readBits count right).length = count :=
  List.length_ofFn

theorem readBits_zero (right : List Bool) : readBits 0 right = [] := rfl

theorem readBits_succ (count : Nat) (right : List Bool) :
    readBits (count + 1) right = right.head?.getD false :: readBits count right.tail := by
  unfold readBits
  rw [List.ofFn_succ]
  apply congrArg₂ List.cons
  · cases right <;> rfl
  · apply congrArg List.ofFn
    funext point
    cases right <;> rfl

theorem rawPayload_getD (value point : Nat) :
    (PSTRTMNatValue017.rawPayload value).getD point false = value.testBit point := by
  calc
    _ = (PSTRTMNatValue017.rawPayload value).getI point :=
      List.getD_default_eq_getI (l := PSTRTMNatValue017.rawPayload value) (n := point)
    _ = (PSTRTMIncrement009.valueDigits (PSTRTMNatValue017.rawPayload value)).testBit point :=
      (PSTRTMNatValue017.testBit_valueDigits _ _).symm
    _ = value.testBit point := by rw [PSTRTMNatValue017.valueDigits_rawPayload]

theorem original_nat_header (value : Nat) (right : List Bool)
    (same : ListBlank.mk right = ListBlank.mk (encodeNat value)) :
    Header (natBits value) (ListBlank.mk (PSTRTMNatValue017.rawPayload value)) right := by
  simp only [Header, same, ListBlank.cons_mk, ListBlank.append_mk, encodeNat,
    PSTRTMNatValue017.rawPayload, List.append_assoc, List.cons_append, List.nil_append]

theorem payload_copy (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (countBit widthBit : Bool) (right left value reverseWord width used : List Bool) :
    TM2.step (program caller)
      (state background 2 memory right (countBit :: left) value reverseWord (widthBit :: width) used) =
      some (state background 2 (true, right.head?.getD false) right.tail left value
        (right.head?.getD false :: reverseWord) width (true :: used)) := by
  change some (TM2.stepAux (program caller 2) memory
    (cells background right (countBit :: left) value reverseWord (widthBit :: width) used)) = _
  simp only [program_two, TM2.stepAux, cells_left, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, jump]
  rw [update_left, cells_right, update_right, cells_width]
  simp only [List.head?_cons, List.tail_cons, presence, Option.isSome_some, Bool.cond_true]
  rw [update_width, cells_reverse, update_reverse, cells_used, update_used]
  rfl

theorem payload_discard (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (countBit : Bool) (right left value reverseWord used : List Bool) :
    TM2.step (program caller)
      (state background 2 memory right (countBit :: left) value reverseWord [] used) =
      some (state background 2 (false, right.head?.getD false) right.tail left value reverseWord [] used) := by
  change some (TM2.stepAux (program caller 2) memory
    (cells background right (countBit :: left) value reverseWord [] used)) = _
  simp only [program_two, TM2.stepAux, cells_left, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, jump]
  rw [update_left, cells_right, update_right, cells_width]
  simp only [List.head?_nil, List.tail_nil, presence, Option.isSome_none, Bool.cond_false]
  rw [update_width]
  rfl

theorem payload_done (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    TM2.step (program caller) (state background 2 memory right [] value reverseWord width used) =
      some (state background 3 (false, false) right [] value reverseWord width used) := by
  change some (TM2.stepAux (program caller 2) memory
    (cells background right [] value reverseWord width used)) = _
  simp only [program_two, TM2.stepAux, cells_left, List.head?_nil, List.tail_nil, capture,
    Option.isSome_none, Option.getD_none, Bool.cond_false, jump]
  rw [update_left]
  rfl

theorem pad_bit (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (widthBit : Bool) (right value reverseWord width used : List Bool) :
    TM2.step (program caller)
      (state background 3 memory right [] value reverseWord (widthBit :: width) used) =
      some (state background 3 (true, widthBit) right [] value
        (false :: reverseWord) width (true :: used)) := by
  change some (TM2.stepAux (program caller 3) memory
    (cells background right [] value reverseWord (widthBit :: width) used)) = _
  simp only [program_three, TM2.stepAux, cells_width, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, jump]
  rw [update_width, cells_reverse, update_reverse, cells_used, update_used]
  rfl

theorem pad_done (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right value reverseWord used : List Bool) :
    TM2.step (program caller) (state background 3 memory right [] value reverseWord [] used) =
      some (state background 4 (false, false) right [] value reverseWord [] used) := by
  change some (TM2.stepAux (program caller 3) memory
    (cells background right [] value reverseWord [] used)) = _
  simp only [program_three, TM2.stepAux, cells_width, List.head?_nil, List.tail_nil, capture,
    Option.isSome_none, Option.getD_none, Bool.cond_false, jump]
  rw [update_width]
  rfl

theorem restore_bit (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (bit : Bool) (right value reverseWord width used : List Bool) :
    TM2.step (program caller)
      (state background 4 memory right [] value (bit :: reverseWord) width used) =
      some (state background 4 (true, bit) right [] (bit :: value) reverseWord
        (true :: width) used.tail) := by
  change some (TM2.stepAux (program caller 4) memory
    (cells background right [] value (bit :: reverseWord) width used)) = _
  simp only [program_four, TM2.stepAux, cells_reverse, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, jump]
  rw [update_reverse, cells_used, update_used, cells_width, update_width, cells_value, update_value]
  rfl

theorem restore_done (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right value width used : List Bool) :
    TM2.step (program caller) (state background 4 memory right [] value [] width used) =
      some (state background 5 (false, false) right [] value [] width used) := by
  change some (TM2.stepAux (program caller 4) memory
    (cells background right [] value [] width used)) = _
  simp only [program_four, TM2.stepAux, cells_reverse, List.head?_nil, List.tail_nil, capture,
    Option.isSome_none, Option.getD_none, Bool.cond_false, jump]
  rw [update_reverse]
  rfl

theorem clear_right_bit (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (bit : Bool) (right value width used : List Bool) :
    TM2.step (program caller) (state background 5 memory (bit :: right) [] value [] width used) =
      some (state background 5 (true, bit) right [] value [] width used) := by
  change some (TM2.stepAux (program caller 5) memory
    (cells background (bit :: right) [] value [] width used)) = _
  simp only [program_five, TM2.stepAux, cells_right, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, jump]
  rw [update_right]
  rfl

theorem clear_right_done (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (value width used : List Bool) :
    TM2.step (program caller) (state background 5 memory [] [] value [] width used) =
      some (state background 6 (false, false) [] [] value [] width used) := by
  change some (TM2.stepAux (program caller 5) memory
    (cells background [] [] value [] width used)) = _
  simp only [program_five, TM2.stepAux, cells_right, List.head?_nil, List.tail_nil, capture,
    Option.isSome_none, Option.getD_none, Bool.cond_false, jump]
  rw [update_right]
  rfl

theorem return_step (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (value width used : List Bool) :
    TM2.step (program caller) (state background 6 memory [] [] value [] width used) =
      some (state background 7 memory [] [] value [] width used) := by
  change some (TM2.stepAux (program caller 6) memory
    (cells background [] [] value [] width used)) = _
  rw [program_six]
  rfl

end PaperProofs.Common.Native.PSTRWordBool.NatWordIO
