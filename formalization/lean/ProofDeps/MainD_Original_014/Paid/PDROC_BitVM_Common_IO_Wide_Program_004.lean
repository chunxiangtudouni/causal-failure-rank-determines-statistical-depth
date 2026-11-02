module

public import Paid.PDROC_BitVM_Common_IO_Wide_Primitives_001
public import Paid.PDROC_BitVM_Common_IO_Program_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Wide

open Turing

abbrev Label := PDROC.BitVM.Common.IO.Bootstrap.Label
abbrev Store := PDROC.BitVM.Common.IO.Bootstrap.Store
abbrev Statement := TM1.Stmt Bool Label Store

/-- Count constructs a fixed literal clearing block. The final program
instantiates 62, selected before all raw inputs, not a runtime loop bound. -/
def clearCode : Nat → Statement → Statement
  | 0, next => next
  | count + 1, next => .write (fun _ _ => false) (.move .right (clearCode count next))

theorem clearCode_support (count : Nat) (next : Statement) (support : Finset Label) :
    TM1.SupportsStmt support (clearCode count next) ↔ TM1.SupportsStmt support next := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

/-- Full tape equality after every specified cell was really cleared. -/
theorem clearCode_overwrite (front left right : List Bool) (saved : Store) (next : Statement) :
    TM1.stepAux (clearCode front.length next) saved (Tape.mk₂ left (front ++ right)) =
      TM1.stepAux next saved (Tape.mk₂ (List.replicate front.length false ++ left) right) := by
  induction front generalizing left with
  | nil => rfl
  | cons bit front ih =>
    simpa [clearCode, TM1.stepAux, Tape.mk₂, List.replicate_add, List.append_assoc] using ih (false :: left)

def runtimeGetters : List (Store → Bool) :=
  [fun _ => true, fun _ => true] ++ List.replicate 59 (fun _ => false) ++
    [fun saved => saved.marked, fun saved => saved.bit, fun _ => true, fun _ => false]

theorem runtimeGetters_value (saved : Store) :
    (runtimeGetters.map (fun getter => getter saved)).reverse = temporaryRow 29 saved.bit saved.marked := by
  simp [runtimeGetters, temporaryRow, rowPrefix, padding]

def writeTemporary65 : Statement :=
  writeBackCode runtimeGetters (.goto (fun _ _ => 12))

def clearAuxiliary65 (next : Statement) : Statement :=
  moveCode .right 3 (clearCode 62 next)

/-- The marker is physically col3; from last col64 the machine really
moves LEFT61. An unmarked row then costs LEFT4, totaling the true stride65. -/
def counterRow65 : Statement :=
  let found := TM1.Stmt.load (fun _ saved => { saved with next := 3 }) (.goto (fun _ _ => 12))
  let clear := TM1.Stmt.write (fun _ _ => false) (moveCode .left 3 found)
  let later := moveCode .left 4 (.goto (fun _ _ => 7))
  let inspect := TM1.Stmt.branch (fun symbol _ => symbol) clear later
  let atMark := moveCode .left 61 inspect
  let absent := TM1.Stmt.load (fun _ saved => { saved with next := 4 }) (.goto (fun _ _ => 12))
  .branch (fun symbol _ => symbol) atMark (.move .right absent)

/-- ONE fixed actual Bool-tape bootstrap for the final Fin32 source.
All ten-field control, input reads, cursor erasure and fixed header/tag/sign
code are reused from the checked 21-label prototype. Only the real row
scan/write/cleanup blocks are widened to 65; Store remains entirely finite. -/
def program (label : Label) : Statement :=
  match label.val with
  | 7 => counterRow65
  | 11 => .branch (fun symbol _ => symbol)
      (moveCode .left 65 (.goto (fun _ _ => 11))) writeTemporary65
  | 12 => .branch (fun symbol _ => symbol)
      (.move .right (.goto (fun _ _ => 13)))
      (moveCode .right 65 (.goto (fun _ _ => 12)))
  | 16 => .branch (fun symbol _ => symbol)
      (moveCode .left 65 (.goto (fun _ _ => 16)))
      (.move .right (.goto (fun _ _ => 17)))
  | 17 => .write (fun _ _ => true) (clearAuxiliary65 (.goto (fun _ _ => 18)))
  | 18 => .branch (fun symbol _ => symbol)
      (.write (fun _ _ => false) (moveCode .left 65 (.goto (fun _ _ => 19))))
      (clearAuxiliary65 (.goto (fun _ _ => 18)))
  | 19 => .branch (fun symbol _ => symbol) .halt
      (moveCode .left 65 (.goto (fun _ _ => 19)))
  | _ => PDROC.BitVM.Common.IO.Bootstrap.program label

theorem supports : TM1.Supports program Finset.univ := by
  exact ⟨by simp, fun label _ =>
    PDROC.BitVM.Common.IO.Bootstrap.statement_support (program label)⟩

theorem initialize_step (input : List Bool) :
    TM1.step program (TM1.init (Γ := Bool) (Λ := Label) (σ := Store) input) =
      some (⟨some 1, ⟨0, 8, false, false, 0⟩,
        Tape.mk₂ [false, true] (true :: input)⟩ : TM1.Cfg Bool Label Store) :=
  PDROC.BitVM.Common.IO.Bootstrap.initialize_step input

/-- Finite Boolean source-read effect, retaining every caller control field. -/
theorem read_bit (saved : Store) (bit previous : Bool) (archive suffix : List Bool) :
    TM1.step program
      (⟨some 9, saved, Tape.mk₂ (previous :: archive) (true :: bit :: suffix)⟩ : TM1.Cfg Bool Label Store) =
      some (⟨some 10, { saved with bit := bit },
        Tape.mk₂ archive (previous :: false :: true :: suffix)⟩ : TM1.Cfg Bool Label Store) := by
  simp [TM1.step, TM1.stepAux, program, PDROC.BitVM.Common.IO.Bootstrap.program, Tape.mk₂]

/-- All 65 cells are truly written. The tape suffix still contains the
real anchor/cursor and every unconsumed source bit. -/
theorem write_row (saved : Store) (right : List Bool) :
    TM1.step program
      (⟨some 11, saved, Tape.mk₂ [] (false :: right)⟩ : TM1.Cfg Bool Label Store) =
      some (⟨some 12, saved, Tape.mk₂ [] (temporaryRow 29 saved.bit saved.marked ++ right)⟩ :
        TM1.Cfg Bool Label Store) := by
  change some (TM1.stepAux (writeBackCode runtimeGetters (.goto (fun _ _ => 12))) saved
    (Tape.mk₂ [] (false :: right))) = _
  rw [writeBackCode_blank, runtimeGetters_value]
  rfl

end PDROC.BitVM.Common.IO.Wide
