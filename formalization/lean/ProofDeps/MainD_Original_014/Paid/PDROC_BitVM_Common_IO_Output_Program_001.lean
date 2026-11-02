module

public import Paid.PDROC_BitVM_Common_IO_Wide_Primitives_001
public import Structure.PA17_TM_RatArithmetic_Unblock_004c

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

abbrev Label := Fin 33

/-- Only actual read bits and finite scan flags. All lengths, row
positions, stack contents and output bytes stay on the physical tape. -/
structure Store where
  bit : Bool
  bottom : Bool
  seen : Bool
  deriving Inhabited, Fintype, DecidableEq

abbrev Statement := TM1.Stmt Bool Label Store

def cfg (label : Label) (saved : Store) (tape : Tape Bool) : TM1.Cfg Bool Label Store :=
  ⟨some label, saved, tape⟩

/-- Fixed code construction: one presence/value pair per compile-time
stack. The final literal code instantiates count=32, never a data width. -/
def presenceCode : Nat → Statement → Statement
  | 0, next => next
  | count + 1, next => .move .right
      (.load (fun symbol saved => { saved with seen := saved.seen || symbol })
        (.move .right (presenceCode count next)))

def markCurrent (next : Label) : Statement :=
  .load (fun symbol saved => { saved with bottom := symbol })
    (.write (fun _ _ => true)
      (Wide.moveCode .right 2
        (.load (fun symbol saved => { saved with bit := symbol })
          (Wide.moveCode .left 2 (Wide.moveCode .right 65 (.goto (fun _ _ => next)))))))

/-- Probe all32 actual presence cells, preserving every old data bit.
Only the first genuinely blank row outside ALL stacks becomes an anchor. -/
def findEnd : Statement :=
  let found : Statement := Wide.moveCode .left 65
    (.write (fun _ _ => true) (Wide.moveCode .right 4 (.goto (fun _ _ => 4))))
  let later : Statement := .goto (fun _ _ => 2)
  .load (fun _ saved => { saved with seen := false })
    (presenceCode 32 (.move .right (.branch (fun _ saved => saved.seen) later found)))

def nativeLabel (label : Fin 20) : Label := ⟨label.val + 11, by have bound := label.isLt; omega⟩

/-- Literal instruction adaptation of the already checked UNMARKED
inverse codec. Each real old TM0 instruction is one real TM1 statement;
its actual HALT returns to the physical header-skip phase. -/
def nativeAction (label : Fin 20) (symbol : Bool) : Statement :=
  match PSTRTMUnblock018.unblockMachine label symbol with
  | none => .goto (fun _ _ => 31)
  | some (next, .move direction) => .move direction (.goto (fun _ _ => nativeLabel next))
  | some (next, .write bit) => .write (fun _ _ => bit) (.goto (fun _ _ => nativeLabel next))

def nativeStatement (label : Fin 20) : Statement :=
  .branch (fun symbol _ => symbol) (nativeAction label true) (nativeAction label false)

/-- Fixed final output adapter, 33 labels and three Bool flags.

From bottom: find stack0's true top, mark one actual source-row cursor,
find the first row outside ALL encoded stacks, and physically shuttle
each source value to `[bit,TRUE]` blocks beyond that row. The source is
read from top to bottom, so its reversed track layout yields the ORIGINAL
byte order. Cursor/anchor searches use col0 and stride65; block searches
use the genuine second-cell flags and stride2. Other track data are kept.

Labels11..30 execute the existing actual unblock machine. Label31 really
skips its unary header and separator;32 really HALTs on the naked stream.
The correctness contract is for the nonempty original Artifact encoding.
-/
def program (label : Label) : Statement :=
  match label.val with
  | 0 => .move .right (.branch (fun symbol _ => symbol)
      (.move .left (Wide.moveCode .right 65 (.goto (fun _ _ => 0))))
      (.move .left (Wide.moveCode .left 65 (.goto (fun _ _ => 1)))))
  | 1 => markCurrent 2
  | 2 => findEnd
  | 3 => .branch (fun symbol _ => symbol)
      (Wide.moveCode .right 4 (.goto (fun _ _ => 4)))
      (Wide.moveCode .right 65 (.goto (fun _ _ => 3)))
  | 4 => .branch (fun symbol _ => symbol)
      (Wide.moveCode .right 2 (.goto (fun _ _ => 4)))
      (.write (fun _ _ => true) (.move .left
        (.write (fun _ saved => saved.bit) (.move .right (.goto (fun _ _ => 5))))))
  | 5 => .branch (fun symbol _ => symbol)
      (Wide.moveCode .left 2 (.goto (fun _ _ => 5)))
      (Wide.moveCode .left 67 (.goto (fun _ _ => 6)))
  | 6 => .branch (fun symbol _ => symbol) (.goto (fun _ _ => 7))
      (Wide.moveCode .left 65 (.goto (fun _ _ => 6)))
  | 7 => .branch (fun _ saved => saved.bottom)
      (Wide.moveCode .right 65 (.goto (fun _ _ => 9)))
      (.write (fun _ _ => false) (Wide.moveCode .left 65 (.goto (fun _ _ => 8))))
  | 8 => markCurrent 3
  | 9 => .branch (fun symbol _ => symbol)
      (Wide.moveCode .right 3 (.goto (fun _ _ => 10)))
      (Wide.moveCode .right 65 (.goto (fun _ _ => 9)))
  | 10 => .goto (fun _ _ => 11)
  | 31 => .branch (fun symbol _ => symbol)
      (.move .right (.goto (fun _ _ => 31)))
      (.move .right (.goto (fun _ _ => 32)))
  | value => if bound : value < 31 then nativeStatement ⟨value - 11, by omega⟩ else .halt

theorem statement_support (statement : Statement) : TM1.SupportsStmt Finset.univ statement := by
  induction statement with
  | move direction next ih => exact ih
  | write value next ih => exact ih
  | load value next ih => exact ih
  | branch predicate yes no yesIH noIH => exact ⟨yesIH, noIH⟩
  | goto target => simp [TM1.SupportsStmt]
  | halt => trivial

theorem supports : TM1.Supports program Finset.univ :=
  ⟨by simp, fun label _ => statement_support (program label)⟩

theorem native_program (label : Fin 20) : program (nativeLabel label) = nativeStatement label := by
  fin_cases label <;> rfl

def embedNative (saved : Store) (source : MachineState 19) : TM1.Cfg Bool Label Store :=
  cfg (nativeLabel source.q) saved source.Tape

/-- The old genuine inverse-codec trace transfers instruction by
instruction to the SAME tape, without decoding digits in host control. -/
theorem native_edge (saved : Store) (before after : MachineState 19)
    (edge : TM0.step PSTRTMUnblock018.unblockMachine before = some after) :
    TM1.step program (embedNative saved before) = some (embedNative saved after) := by
  rcases before with ⟨label, tape⟩
  simp only [TM0.step] at edge
  cases instruction : PSTRTMUnblock018.unblockMachine label tape.head with
  | none => simp only [instruction, Option.map_none] at edge; contradiction
  | some operation =>
    rcases operation with ⟨next, action⟩
    cases action with
    | move direction =>
      simp only [instruction, Option.map_some, Option.some.injEq] at edge
      subst after
      change some (TM1.stepAux (program (nativeLabel label)) saved tape) = _
      rw [native_program]
      cases symbol : tape.head <;>
        simp_all [nativeStatement, nativeAction, TM1.stepAux, embedNative, cfg]
    | write bit =>
      simp only [instruction, Option.map_some, Option.some.injEq] at edge
      subst after
      change some (TM1.stepAux (program (nativeLabel label)) saved tape) = _
      rw [native_program]
      cases symbol : tape.head <;>
        simp_all [nativeStatement, nativeAction, TM1.stepAux, embedNative, cfg]

end PDROC.BitVM.Common.IO.Output
