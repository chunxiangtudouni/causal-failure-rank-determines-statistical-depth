module

public import Paid.PDROC_BitVM_Common_TM1_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.BitVM.Common.IO

open Turing

/-- All seven cells are physically written. The last two TRUE cells are
temporary scan markers; col3 is the current numeric header's unary DATA.
They will be actually cleared by the final pass, not quotiented away. -/
def temporaryRow (bit marked : Bool) : List Bool :=
  [false, true, bit, marked, false, true, true]

abbrev EmitLabel := Fin 6
abbrev EmitState := TM1.Cfg Bool EmitLabel Bool

def emitState (label : Option EmitLabel) (saved : Bool) (left right : List Bool) : EmitState :=
  ⟨label, saved, Tape.mk₂ left right⟩

def sevenMoves (direction : Dir) (next : TM1.Stmt Bool EmitLabel Bool) :
    TM1.Stmt Bool EmitLabel Bool :=
  .move direction (.move direction (.move direction (.move direction
    (.move direction (.move direction (.move direction next))))))

def writeTemporaryRow (marked : Bool) : TM1.Stmt Bool EmitLabel Bool :=
  let col0 := TM1.Stmt.write (fun _ _ => false) (.goto (fun _ _ => 3))
  let col1 := TM1.Stmt.write (fun _ _ => true) (.move .left col0)
  let col2 := TM1.Stmt.write (fun _ saved => saved) (.move .left col1)
  let col3 := TM1.Stmt.write (fun _ _ => marked) (.move .left col2)
  let col4 := TM1.Stmt.write (fun _ _ => false) (.move .left col3)
  let col5 := TM1.Stmt.write (fun _ _ => true) (.move .left col4)
  TM1.Stmt.write (fun _ _ => true) (.move .left col5)

/-- No word, input width or list appears in this six-label controller.
The one saved Bool is read from the genuine next source cell. -/
def emitProgram (marked : Bool) (label : EmitLabel) : TM1.Stmt Bool EmitLabel Bool :=
  match label.val with
  | 0 => .move .right (.load (fun symbol _ => symbol)
      (.write (fun _ _ => true) (.move .left (.write (fun _ _ => false)
        (.move .left (.goto (fun _ _ => 1)))))))
  | 1 => .branch (fun symbol _ => symbol)
      (.move .left (.goto (fun _ _ => 2)))
      (.move .left (.goto (fun _ _ => 1)))
  | 2 => .branch (fun symbol _ => symbol)
      (sevenMoves .left (.goto (fun _ _ => 2)))
      (writeTemporaryRow marked)
  | 3 => .branch (fun symbol _ => symbol)
      (.move .right (.goto (fun _ _ => 4)))
      (sevenMoves .right (.goto (fun _ _ => 3)))
  | 4 => .branch (fun symbol _ => symbol)
      (.goto (fun _ _ => 5))
      (.move .right (.goto (fun _ _ => 4)))
  | _ => .halt

theorem emit_support (marked : Bool) : TM1.Supports (emitProgram marked) Finset.univ := by
  constructor
  · simp
  · intro label _
    fin_cases label <;> simp [emitProgram, sevenMoves, writeTemporaryRow, TM1.SupportsStmt]

theorem emit_read (marked saved bit previous : Bool) (archive suffix : List Bool) :
    TM1.step (emitProgram marked)
      (emitState (some 0) saved (previous :: archive) (true :: bit :: suffix)) =
      some (emitState (some 1) bit archive (previous :: false :: true :: suffix)) := by
  simp [TM1.step, TM1.stepAux, emitProgram, emitState, Tape.mk₂]

theorem emit_anchor_false (marked saved previous : Bool) (archive right : List Bool) :
    TM1.step (emitProgram marked)
      (emitState (some 1) saved (previous :: archive) (false :: right)) =
      some (emitState (some 1) saved archive (previous :: false :: right)) := by
  simp [TM1.step, TM1.stepAux, emitProgram, emitState, Tape.mk₂]

theorem emit_anchor_true (marked saved previous : Bool) (archive right : List Bool) :
    TM1.step (emitProgram marked)
      (emitState (some 1) saved (previous :: archive) (true :: right)) =
      some (emitState (some 2) saved archive (previous :: true :: right)) := by
  simp [TM1.step, TM1.stepAux, emitProgram, emitState, Tape.mk₂]

/-- The only writing macro prepends one row in genuine left blank space.
Its full old right suffix, including the actual anchor/cursor/source, stays. -/
theorem emit_write_row (marked bit : Bool) (right : List Bool) :
    TM1.step (emitProgram marked) (emitState (some 2) bit [] (false :: right)) =
      some (emitState (some 3) bit [] (temporaryRow bit marked ++ right)) := by
  simp [TM1.step, TM1.stepAux, emitProgram, writeTemporaryRow, emitState, temporaryRow, Tape.mk₂]

theorem emit_skip_row (marked saved bit oldMark previous : Bool)
    (archive right : List Bool) :
    TM1.step (emitProgram marked)
      (emitState (some 2) saved
        ([true, false, oldMark, bit, true, false] ++ previous :: archive) (true :: right)) =
      some (emitState (some 2) saved archive (previous :: (temporaryRow bit oldMark ++ right))) := by
  simp [TM1.step, TM1.stepAux, emitProgram, sevenMoves, emitState, temporaryRow, Tape.mk₂]

theorem emit_skip_last_row (marked saved bit oldMark : Bool) (right : List Bool) :
    TM1.step (emitProgram marked)
      (emitState (some 2) saved [true, false, oldMark, bit, true, false] (true :: right)) =
      some (emitState (some 2) saved [] (false :: (temporaryRow bit oldMark ++ right))) := by
  simp [TM1.step, TM1.stepAux, emitProgram, sevenMoves, emitState, temporaryRow, Tape.mk₂]

theorem emit_return_row (marked saved bit oldMark : Bool) (left right : List Bool) :
    TM1.step (emitProgram marked)
      (emitState (some 3) saved left (temporaryRow bit oldMark ++ right)) =
      some (emitState (some 3) saved ((temporaryRow bit oldMark).reverse ++ left) right) := by
  simp [TM1.step, TM1.stepAux, emitProgram, sevenMoves, emitState, temporaryRow, Tape.mk₂]

theorem emit_return_anchor (marked saved : Bool) (left right : List Bool) :
    TM1.step (emitProgram marked) (emitState (some 3) saved left (true :: right)) =
      some (emitState (some 4) saved (true :: left) right) := by
  simp [TM1.step, TM1.stepAux, emitProgram, emitState, Tape.mk₂]

theorem emit_cursor_false (marked saved : Bool) (left right : List Bool) :
    TM1.step (emitProgram marked) (emitState (some 4) saved left (false :: right)) =
      some (emitState (some 4) saved (false :: left) right) := by
  simp [TM1.step, TM1.stepAux, emitProgram, emitState, Tape.mk₂]

theorem emit_cursor_found (marked saved : Bool) (left right : List Bool) :
    TM1.step (emitProgram marked) (emitState (some 4) saved left (true :: right)) =
      some (emitState (some 5) saved left (true :: right)) := by
  simp [TM1.step, TM1.stepAux, emitProgram, emitState, Tape.mk₂]

theorem emit_halt (marked saved : Bool) (left right : List Bool) :
    TM1.step (emitProgram marked) (emitState (some 5) saved left right) =
      some (emitState none saved left right) := by
  rfl

end PDROC.BitVM.Common.IO
