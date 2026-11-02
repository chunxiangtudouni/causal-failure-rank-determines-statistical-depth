module

public import Paid.PDROC_BitVM_Common_IO_Paths_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

variable {Label Store : Type*}

theorem tape_left_blank (left right : List Bool) :
    Tape.mk₂ (left ++ [false]) right = Tape.mk₂ left right := by
  have blank : ListBlank.mk (left ++ [false]) = ListBlank.mk left :=
    Quotient.sound' (Or.inr ⟨1, rfl⟩)
  unfold Tape.mk₂
  rw [blank]

theorem tape_right_blank (left right : List Bool) :
    Tape.mk₂ left (right ++ [false]) = Tape.mk₂ left right := by
  have blank : ListBlank.mk (right ++ [false]) = ListBlank.mk right :=
    Quotient.sound' (Or.inr ⟨1, rfl⟩)
  unfold Tape.mk₂
  rw [blank]

/-- Count is a CODE-CONSTRUCTION parameter, selected before the input.
No runtime width or loop count is stored in Store or the finite alphabet. -/
def moveCode (direction : Dir) : Nat → TM1.Stmt Bool Label Store → TM1.Stmt Bool Label Store
  | 0, next => next
  | count + 1, next => .move direction (moveCode direction count next)

theorem moveCode_support (direction : Dir) (count : Nat) (next : TM1.Stmt Bool Label Store)
    (support : Finset Label) :
    TM1.SupportsStmt support (moveCode direction count next) ↔ TM1.SupportsStmt support next := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

/-- These are the real ordinary RIGHT moves across the stated cells. -/
theorem moveCode_right (front left right : List Bool) (saved : Store)
    (next : TM1.Stmt Bool Label Store) :
    TM1.stepAux (moveCode .right front.length next) saved (Tape.mk₂ left (front ++ right)) =
      TM1.stepAux next saved (Tape.mk₂ (front.reverse ++ left) right) := by
  induction front generalizing left with
  | nil => rfl
  | cons bit front ih =>
    simpa [moveCode, TM1.stepAux, Tape.mk₂, List.reverse_cons, List.append_assoc] using ih (bit :: left)

/-- These are the real ordinary LEFT moves across the stated cells. -/
theorem moveCode_left (front left right : List Bool) (saved : Store)
    (next : TM1.Stmt Bool Label Store) :
    TM1.stepAux (moveCode .left front.length next) saved (Tape.mk₂ (front ++ left) right) =
      TM1.stepAux next saved (Tape.mk₂ left (front.reverse ++ right)) := by
  induction front generalizing right with
  | nil => rfl
  | cons bit front ih =>
    simpa [moveCode, TM1.stepAux, Tape.mk₂, List.reverse_cons, List.append_assoc] using ih (bit :: right)

/-- One fixed getter for each output cell. The getter list is code, not
input data: for 32 tracks it consists of 65 compile-time expressions.
The extra final RIGHT restores the actual head after the final LEFT. -/
def writeBackCode : List (Store → Bool) → TM1.Stmt Bool Label Store → TM1.Stmt Bool Label Store
  | [], next => .move .right next
  | value :: values, next => .write (fun _ saved => value saved)
      (.move .left (writeBackCode values next))

theorem writeBackCode_support (values : List (Store → Bool)) (next : TM1.Stmt Bool Label Store)
    (support : Finset Label) :
    TM1.SupportsStmt support (writeBackCode values next) ↔ TM1.SupportsStmt support next := by
  induction values with
  | nil => rfl
  | cons value values ih => exact ih

/-- Every cell is genuinely written into left blank space. The whole
old right suffix is retained, including anchor/cursor and unread RAW6.
Host map/reverse below only specify the proved endpoint of those writes. -/
theorem writeBackCode_blank (values : List (Store → Bool)) (right : List Bool) (saved : Store)
    (next : TM1.Stmt Bool Label Store) :
    TM1.stepAux (writeBackCode values next) saved (Tape.mk₂ [] (false :: right)) =
      TM1.stepAux next saved (Tape.mk₂ [] ((values.map (fun value => value saved)).reverse ++ right)) := by
  induction values generalizing right with
  | nil =>
    have moved : (Tape.mk₂ [] (false :: right)).move .right = Tape.mk₂ [] right := by
      calc
        (Tape.mk₂ [] (false :: right)).move .right = Tape.mk₂ [false] right := by simp [Tape.mk₂]
        _ = Tape.mk₂ [] right := tape_left_blank [] right
    simp only [writeBackCode, TM1.stepAux, List.map_nil, List.reverse_nil, List.nil_append, moved]
  | cons value values ih =>
    simpa [writeBackCode, TM1.stepAux, Tape.mk₂, List.reverse_cons, List.append_assoc] using
      ih (value saved :: right)



/-- extraPairs is chosen when constructing the machine, before every
input. Final VM uses 29: 32 stacks, 65-bit rows, 59 internal FALSE cells. -/
def padding (extraPairs : Nat) : Nat := 2 * extraPairs + 1

def stride (extraPairs : Nat) : Nat := 2 * extraPairs + 7

def rowPrefix (extraPairs : Nat) (bit marked : Bool) : List Bool :=
  [false, true, bit, marked] ++ List.replicate (padding extraPairs) false ++ [true]

def temporaryRow (extraPairs : Nat) (bit marked : Bool) : List Bool :=
  rowPrefix extraPairs bit marked ++ [true]

def cleanRow (extraPairs : Nat) (bottom bit : Bool) : List Bool :=
  [bottom, true, bit] ++ List.replicate (padding extraPairs + 3) false

def outputGetters (extraPairs : Nat) (marked : Bool) : List (Bool → Bool) :=
  [fun _ => true, fun _ => true] ++
    List.replicate (padding extraPairs) (fun _ => false) ++
    [fun _ => marked, id, fun _ => true, fun _ => false]

theorem rowPrefix_length (extraPairs : Nat) (bit marked : Bool) :
    (rowPrefix extraPairs bit marked).length + 1 = stride extraPairs := by
  simp only [rowPrefix, padding, stride, List.length_append, List.length_cons,
    List.length_nil, List.length_replicate]
  omega

theorem temporaryRow_length (extraPairs : Nat) (bit marked : Bool) :
    (temporaryRow extraPairs bit marked).length = stride extraPairs := by
  simpa only [temporaryRow, List.length_append, List.length_cons, List.length_nil] using
    rowPrefix_length extraPairs bit marked

theorem cleanRow_length (extraPairs : Nat) (bottom bit : Bool) :
    (cleanRow extraPairs bottom bit).length = stride extraPairs := by
  simp only [cleanRow, padding, stride, List.length_append, List.length_cons,
    List.length_nil, List.length_replicate]
  omega

theorem outputGetters_value (extraPairs : Nat) (marked bit : Bool) :
    ((outputGetters extraPairs marked).map (fun getter => getter bit)).reverse =
      temporaryRow extraPairs bit marked := by
  simp [outputGetters, temporaryRow, rowPrefix, List.reverse_append, List.append_assoc]

/-- SAME finite six-label / one-Bool-store emitter. Stride and zero padding
are compiled into its fixed syntax; they are never runtime tape inputs. -/
def emitProgram (extraPairs : Nat) (marked : Bool) (label : EmitLabel) : TM1.Stmt Bool EmitLabel Bool :=
  match label.val with
  | 0 => .move .right (.load (fun symbol _ => symbol)
      (.write (fun _ _ => true) (.move .left (.write (fun _ _ => false)
        (.move .left (.goto (fun _ _ => 1)))))))
  | 1 => .branch (fun symbol _ => symbol)
      (.move .left (.goto (fun _ _ => 2)))
      (.move .left (.goto (fun _ _ => 1)))
  | 2 => .branch (fun symbol _ => symbol)
      (moveCode .left (stride extraPairs) (.goto (fun _ _ => 2)))
      (writeBackCode (outputGetters extraPairs marked) (.goto (fun _ _ => 3)))
  | 3 => .branch (fun symbol _ => symbol)
      (.move .right (.goto (fun _ _ => 4)))
      (moveCode .right (stride extraPairs) (.goto (fun _ _ => 3)))
  | 4 => .branch (fun symbol _ => symbol)
      (.goto (fun _ _ => 5))
      (.move .right (.goto (fun _ _ => 4)))
  | _ => .halt

theorem emit_support (extraPairs : Nat) (marked : Bool) :
    TM1.Supports (emitProgram extraPairs marked) Finset.univ := by
  constructor
  · simp
  · intro label _
    fin_cases label <;> simp [emitProgram, moveCode_support, writeBackCode_support, TM1.SupportsStmt]

theorem emit_read (extraPairs : Nat) (marked saved bit previous : Bool) (archive suffix : List Bool) :
    TM1.step (emitProgram extraPairs marked)
      (emitState (some 0) saved (previous :: archive) (true :: bit :: suffix)) =
      some (emitState (some 1) bit archive (previous :: false :: true :: suffix)) :=
  PDROC.BitVM.Common.IO.emit_read marked saved bit previous archive suffix

theorem emit_anchor_false (extraPairs : Nat) (marked saved previous : Bool) (archive right : List Bool) :
    TM1.step (emitProgram extraPairs marked)
      (emitState (some 1) saved (previous :: archive) (false :: right)) =
      some (emitState (some 1) saved archive (previous :: false :: right)) :=
  PDROC.BitVM.Common.IO.emit_anchor_false marked saved previous archive right

theorem emit_anchor_true (extraPairs : Nat) (marked saved previous : Bool) (archive right : List Bool) :
    TM1.step (emitProgram extraPairs marked)
      (emitState (some 1) saved (previous :: archive) (true :: right)) =
      some (emitState (some 2) saved archive (previous :: true :: right)) :=
  PDROC.BitVM.Common.IO.emit_anchor_true marked saved previous archive right

theorem emit_write_row (extraPairs : Nat) (marked bit : Bool) (right : List Bool) :
    TM1.step (emitProgram extraPairs marked) (emitState (some 2) bit [] (false :: right)) =
      some (emitState (some 3) bit [] (temporaryRow extraPairs bit marked ++ right)) := by
  change some (TM1.stepAux
    (writeBackCode (outputGetters extraPairs marked) (.goto (fun _ _ => 3))) bit
      (Tape.mk₂ [] (false :: right))) = _
  rw [writeBackCode_blank, outputGetters_value]
  rfl

theorem emit_skip_row (extraPairs : Nat) (marked saved bit oldMark previous : Bool)
    (archive right : List Bool) :
    TM1.step (emitProgram extraPairs marked)
      (emitState (some 2) saved ((rowPrefix extraPairs bit oldMark).reverse ++ previous :: archive)
        (true :: right)) =
      some (emitState (some 2) saved archive
        (previous :: (temporaryRow extraPairs bit oldMark ++ right))) := by
  have count : ((rowPrefix extraPairs bit oldMark).reverse ++ [previous]).length = stride extraPairs := by
    simpa only [List.length_append, List.length_reverse, List.length_cons, List.length_nil] using
      rowPrefix_length extraPairs bit oldMark
  have moved := moveCode_left ((rowPrefix extraPairs bit oldMark).reverse ++ [previous]) archive
    (true :: right) saved (TM1.Stmt.goto (fun _ _ => (2 : EmitLabel)))
  rw [count] at moved
  change some (TM1.stepAux (moveCode .left (stride extraPairs) (.goto (fun _ _ => 2))) saved
    (Tape.mk₂ ((rowPrefix extraPairs bit oldMark).reverse ++ previous :: archive) (true :: right))) = _
  simpa [emitState, temporaryRow, TM1.stepAux, List.reverse_append, List.append_assoc] using congrArg some moved

theorem emit_skip_last_row (extraPairs : Nat) (marked saved bit oldMark : Bool) (right : List Bool) :
    TM1.step (emitProgram extraPairs marked)
      (emitState (some 2) saved (rowPrefix extraPairs bit oldMark).reverse (true :: right)) =
      some (emitState (some 2) saved [] (false :: (temporaryRow extraPairs bit oldMark ++ right))) := by
  simpa [emitState, tape_left_blank] using
    emit_skip_row extraPairs marked saved bit oldMark false [] right

theorem emit_return_row (extraPairs : Nat) (marked saved bit oldMark : Bool) (left right : List Bool) :
    TM1.step (emitProgram extraPairs marked)
      (emitState (some 3) saved left (temporaryRow extraPairs bit oldMark ++ right)) =
      some (emitState (some 3) saved ((temporaryRow extraPairs bit oldMark).reverse ++ left) right) := by
  have moved := moveCode_right (temporaryRow extraPairs bit oldMark) left right saved
    (TM1.Stmt.goto (fun _ _ => (3 : EmitLabel)))
  rw [temporaryRow_length] at moved
  change some (TM1.stepAux (moveCode .right (stride extraPairs) (.goto (fun _ _ => 3))) saved
    (Tape.mk₂ left (temporaryRow extraPairs bit oldMark ++ right))) = _
  exact congrArg some moved

theorem emit_return_anchor (extraPairs : Nat) (marked saved : Bool) (left right : List Bool) :
    TM1.step (emitProgram extraPairs marked) (emitState (some 3) saved left (true :: right)) =
      some (emitState (some 4) saved (true :: left) right) :=
  PDROC.BitVM.Common.IO.emit_return_anchor marked saved left right

theorem emit_cursor_false (extraPairs : Nat) (marked saved : Bool) (left right : List Bool) :
    TM1.step (emitProgram extraPairs marked) (emitState (some 4) saved left (false :: right)) =
      some (emitState (some 4) saved (false :: left) right) :=
  PDROC.BitVM.Common.IO.emit_cursor_false marked saved left right

theorem emit_cursor_found (extraPairs : Nat) (marked saved : Bool) (left right : List Bool) :
    TM1.step (emitProgram extraPairs marked) (emitState (some 4) saved left (true :: right)) =
      some (emitState (some 5) saved left (true :: right)) :=
  PDROC.BitVM.Common.IO.emit_cursor_found marked saved left right

end PDROC.BitVM.Common.IO.Wide
