module

public import Common.PSTR_WordBool_RawOutput_Source001
public import Common.PSTR_WordBool_RawInit_Shape001
public import Common.PSTR_TM_UnblockTrace_019

/-! The fixed eleven-label Bool TM1 extraction protocol. Source cells are
read before a saved bit is carried in one of two finite labels. The extra
west guard is genuinely created by the initializer, not caller-provided. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

abbrev Label := Fin 11
abbrev Statement := TM1.Stmt Bool Label Unit
abbrev State := TM1.Cfg Bool Label Unit

/-- The only instantiations in machine code are constants 1,2,3,6,30,33,34. -/
def mv (count : Nat) (direction : Dir) (next : Statement) : Statement :=
  (TM1.Stmt.move direction)^[count] next

def jump (label : Label) : Statement := .goto (fun _ _ => label)
def put (bit : Bool) (next : Statement) : Statement := .write (fun _ _ => bit) next
def readBit (yes no : Statement) : Statement := .branch (fun bit _ => bit) yes no

def shuttle (bit : Bool) : Label := if bit then 4 else 3
def seekOutput (bit : Bool) : Label := if bit then 6 else 5

/-- Labels:0 initialize,1 next source,2 read source presence/data,
3/4 return to guard with saved bit,5/6 push flagged bit west,7 return east,
8 erase all marked source rows,9 find output,10 seek its actual first DATA. -/
def sourceMachine (label : Label) : Statement :=
  match label.val with
  | 0 => put false (mv 33 .left (mv 3 .right (put true (mv 30 .right (jump 1)))))
  | 1 => readBit (mv 33 .right (jump 1)) (mv 1 .right (jump 2))
  | 2 => readBit
      (mv 1 .left (put true (mv 1 .right (put false (mv 1 .right
        (readBit (put false (mv 1 .right (jump (shuttle true))))
          (put false (mv 1 .right (jump (shuttle false))))))))))
      (mv 1 .left (jump 8))
  | 3 => readBit (mv 6 .left (jump (seekOutput false))) (mv 33 .left (jump (shuttle false)))
  | 4 => readBit (mv 6 .left (jump (seekOutput true))) (mv 33 .left (jump (shuttle true)))
  | 5 => readBit (mv 2 .left (jump 5)) (put true (mv 1 .left (put false (mv 3 .right (jump 7)))))
  | 6 => readBit (mv 2 .left (jump 6)) (put true (mv 1 .left (put true (mv 3 .right (jump 7)))))
  | 7 => readBit (mv 2 .right (jump 7)) (mv 34 .right (jump 1))
  | 8 => mv 3 .right (readBit
      (put false (mv 3 .left (put false (jump 9))))
      (mv 3 .left (put false (mv 33 .left (jump 8)))))
  | 9 => mv 3 .left (jump 10)
  | _ => readBit (mv 2 .left (jump 10)) (mv 1 .right .halt)

theorem mv_step (count : Nat) (direction : Dir) (next : Statement) (tape : Tape Bool) :
    TM1.stepAux (mv count direction next) () tape =
      TM1.stepAux next () ((Tape.move direction)^[count] tape) := by
  unfold mv
  induction count generalizing tape with
  | zero => rfl
  | succ count ih =>
    rw [Function.iterate_succ', Function.iterate_succ]
    simp only [TM1.stepAux, Function.comp_apply]
    exact ih _

private theorem supports_statement (statement : Statement) :
    TM1.SupportsStmt Finset.univ statement := by
  induction statement <;> simp_all [TM1.SupportsStmt]

theorem source_closed : TM1.Supports sourceMachine Finset.univ := by
  exact ⟨Finset.mem_univ _, fun label _ => supports_statement (sourceMachine label)⟩

def cfg (label : Label) (left right : List Bool) : State :=
  ⟨some label, (), Tape.mk₂ left right⟩

def guardRow : List Bool := [false,false,false,true] ++ List.replicate 29 false
def doneRow : List Bool := true :: List.replicate 32 false
def dataRow (bit : Bool) : List Bool := false :: true :: bit :: List.replicate 30 false
def doneRows (count : Nat) : List Bool := (List.replicate count doneRow).flatten
def dataRows (bits : List Bool) : List Bool := bits.flatMap dataRow

/-- Nearest-west-first: two actual FALSE cells isolate all output flags
from the guard. New pairs are pushed at their actual west boundary. -/
def workLeft (previous : List Bool) : List Bool :=
  [false,false] ++ (PSTRTMIncrement009.blocks previous).reverse

def loopCfg (previous remaining : List Bool) : State :=
  cfg 1 (guardRow.reverse ++ workLeft previous)
    (doneRows previous.length ++ dataRows remaining)

def finishCfg (bits : List Bool) : State :=
  ⟨none, (), Tape.mk₁ (PSTRTMIncrement009.blocks bits)⟩

def loopClock (previous remaining : List Bool) : Nat :=
  2*remaining.length^2+4*previous.length*remaining.length+
    7*remaining.length+3*previous.length+6

theorem row_lengths : guardRow.length=33 ∧ doneRow.length=33 ∧
    (∀ bit, (dataRow bit).length=33) := by
  exact ⟨rfl,rfl,fun _ => rfl⟩

theorem clock_step (previous later : List Bool) (bit : Bool) :
    loopClock previous (bit :: later) =
      4*previous.length+6+loopClock (bit :: previous) later := by
  simp only [loopClock, List.length_cons]
  ring

end PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract
