module

public import Paid.PDROC_BitVM_Common_IO_Emit_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Common.IO.Bootstrap

open Turing

abbrev Label := Fin 21

/-- Only fixed finite control. All input-dependent widths and counters
are represented by actual temporary-row marks on the Bool tape. -/
structure Store where
  field : Fin 10
  remaining : Fin 9
  bit : Bool
  marked : Bool
  next : Fin 6
  deriving Inhabited, Fintype, DecidableEq

abbrev Statement := TM1.Stmt Bool Label Store

def moveSeven (direction : Dir) (next : Statement) : Statement :=
  .move direction (.move direction (.move direction (.move direction
    (.move direction (.move direction (.move direction next))))))

def writeTemporary : Statement :=
  let col0 := TM1.Stmt.write (fun _ _ => false) (.goto (fun _ _ => 12))
  let col1 := TM1.Stmt.write (fun _ _ => true) (.move .left col0)
  let col2 := TM1.Stmt.write (fun _ saved => saved.bit) (.move .left col1)
  let col3 := TM1.Stmt.write (fun _ saved => saved.marked) (.move .left col2)
  let col4 := TM1.Stmt.write (fun _ _ => false) (.move .left col3)
  let col5 := TM1.Stmt.write (fun _ _ => true) (.move .left col4)
  TM1.Stmt.write (fun _ _ => true) (.move .left col5)

def clearAuxiliary (next : Statement) : Statement :=
  let col6 := TM1.Stmt.write (fun _ _ => false) (.move .right next)
  let col5 := TM1.Stmt.write (fun _ _ => false) (.move .right col6)
  let col4 := TM1.Stmt.write (fun _ _ => false) (.move .right col5)
  let col3 := TM1.Stmt.write (fun _ _ => false) (.move .right col4)
  .move .right (.move .right (.move .right col3))

def followingField (field : Fin 10) : Fin 10 :=
  if safe : field.val + 1 < 10 then ⟨field.val + 1, safe⟩ else field

/-- After natural field0 skip field1's tag; after odd field1/3/5/7
skip the next rational tag/sign. Even fields2/4/6/8 go straight to DEN. -/
def followingSkip (field : Fin 10) : Fin 9 :=
  if field.val = 0 then 1 else if field.val % 2 = 1 then 2 else 0

def decrement (remaining : Fin 9) : Fin 9 :=
  ⟨remaining.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) remaining.isLt⟩

def dispatch (next : Fin 6) : Label :=
  match next.val with
  | 0 => 1 -- fixed header/tag/sign bits
  | 1 => 2 -- unary header
  | 2 => 5 -- search/decrement unary tape marks
  | 3 => 3 -- emit one payload bit
  | 4 => 4 -- advance the fixed numeric-field index
  | _ => 14 -- original footer was emitted; clean up physically

def initializeCode : Statement :=
  let cursor := TM1.Stmt.write (fun _ _ => true) (.goto (fun _ _ => 1))
  let anchor := TM1.Stmt.write (fun _ _ => true) (.move .right (.move .right cursor))
  .load (fun _ _ => ⟨0, 8, false, false, 0⟩)
    (.move .left (.move .left (.move .left anchor)))

def counterRow : Statement :=
  let found := TM1.Stmt.load (fun _ saved => { saved with next := 3 }) (.goto (fun _ _ => 12))
  let clear := TM1.Stmt.write (fun _ _ => false) (.move .left (.move .left (.move .left found)))
  let later := TM1.Stmt.move .left (.move .left (.move .left (.move .left (.goto (fun _ _ => 7)))))
  let inspect := TM1.Stmt.branch (fun symbol _ => symbol) clear later
  let atMark := TM1.Stmt.move .left (.move .left (.move .left inspect))
  let absent := TM1.Stmt.load (fun _ saved => { saved with next := 4 }) (.goto (fun _ _ => 12))
  .branch (fun symbol _ => symbol) atMark (.move .right absent)

/-- A fixed raw6 bootloader: 21 labels and one finite store. It consumes
the original seven-bit list header, two natural Cells, four rational Cells
(ten self-delimited natural fields), then exactly the original TRUE footer.
The unbounded counter lives in col3 of rows, never in Store or labels. -/
def program (label : Label) : Statement :=
  match label.val with
  | 0 => initializeCode
  | 1 => .branch (fun _ saved => decide (saved.remaining.val = 0))
      (.goto (fun _ _ => 2))
      (.load (fun _ saved => { saved with remaining := decrement saved.remaining, marked := false, next := 0 })
        (.goto (fun _ _ => 9)))
  | 2 => .move .right (.load (fun symbol saved =>
        { saved with marked := symbol, next := if symbol then 1 else 2 })
      (.move .left (.goto (fun _ _ => 9))))
  | 3 => .load (fun _ saved => { saved with marked := false, next := 2 })
      (.goto (fun _ _ => 9))
  | 4 => .branch (fun _ saved => decide (saved.field.val = 9))
      (.load (fun _ saved => { saved with marked := false, next := 5 }) (.goto (fun _ _ => 9)))
      (.load (fun _ saved => { saved with field := followingField saved.field, remaining := followingSkip saved.field })
        (.goto (fun _ _ => 1)))
  | 5 => .move .left (.goto (fun _ _ => 6))
  | 6 => .branch (fun symbol _ => symbol)
      (.move .left (.goto (fun _ _ => 7)))
      (.move .left (.goto (fun _ _ => 6)))
  | 7 => counterRow
  | 9 => .move .right (.load (fun symbol saved => { saved with bit := symbol })
      (.write (fun _ _ => true) (.move .left (.write (fun _ _ => false)
        (.move .left (.goto (fun _ _ => 10)))))))
  | 10 => .branch (fun symbol _ => symbol)
      (.move .left (.goto (fun _ _ => 11)))
      (.move .left (.goto (fun _ _ => 10)))
  | 11 => .branch (fun symbol _ => symbol)
      (moveSeven .left (.goto (fun _ _ => 11))) writeTemporary
  | 12 => .branch (fun symbol _ => symbol)
      (.move .right (.goto (fun _ _ => 13)))
      (moveSeven .right (.goto (fun _ _ => 12)))
  | 13 => .branch (fun symbol _ => symbol)
      (.goto (fun _ saved => dispatch saved.next))
      (.move .right (.goto (fun _ _ => 13)))
  | 14 => .write (fun _ _ => false) (.move .left (.goto (fun _ _ => 15)))
  | 15 => .branch (fun symbol _ => symbol)
      (.move .left (.goto (fun _ _ => 16)))
      (.move .left (.goto (fun _ _ => 15)))
  | 16 => .branch (fun symbol _ => symbol)
      (moveSeven .left (.goto (fun _ _ => 16)))
      (.move .right (.goto (fun _ _ => 17)))
  | 17 => .write (fun _ _ => true) (clearAuxiliary (.goto (fun _ _ => 18)))
  | 18 => .branch (fun symbol _ => symbol)
      (.write (fun _ _ => false) (moveSeven .left (.goto (fun _ _ => 19))))
      (clearAuxiliary (.goto (fun _ _ => 18)))
  | 19 => .branch (fun symbol _ => symbol) .halt
      (moveSeven .left (.goto (fun _ _ => 19)))
  | _ => .halt

theorem statement_support (statement : Statement) : TM1.SupportsStmt Finset.univ statement := by
  induction statement with
  | move direction next ih => exact ih
  | write value next ih => exact ih
  | load value next ih => exact ih
  | branch predicate yes no yesIH noIH => exact ⟨yesIH, noIH⟩
  | goto target => simp [TM1.SupportsStmt]
  | halt => trivial

theorem supports : TM1.Supports program Finset.univ := by
  exact ⟨by simp, fun label _ => statement_support (program label)⟩

/-- True original TM1 init supplies the real blank left workspace. Five
charged moves and two actual writes install anchor/cursor at gap=1. -/
theorem initialize_step (input : List Bool) :
    TM1.step program (TM1.init (Γ := Bool) (Λ := Label) (σ := Store) input) =
      some (⟨some 1, ⟨0, 8, false, false, 0⟩,
        Tape.mk₂ [false, true] (true :: input)⟩ : TM1.Cfg Bool Label Store) := by
  simp [TM1.step, TM1.stepAux, TM1.init, program, initializeCode, Tape.mk₁, Tape.mk₂, Fin.default_eq_zero]

end PDROC.BitVM.Common.IO.Bootstrap
