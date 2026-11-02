module

public import Paid.PDCompute_SolverRuntimeCommands_085

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

/-- Fixed instructions only: B, row, column and k are genuinely read
from live Header47/19/20/4. Literal constants are only1,6,48. -/
def rowPointerCommands : List RuntimeCommand :=
  [.scalar (.constant 46 (.natural 1)),.natural .subtract 19 46 35,
   .natural .add 4 46 38,.natural .multiply 35 38 35,.natural .add 35 20 35,
   .scalar (.constant 46 (.natural 6)),.natural .multiply 46 35 35,
   .scalar (.constant 46 (.natural 48)),.natural .add 46 35 35,.natural .add 47 35 35,
   .scalar (.constant 46 (.natural 6)),.natural .subtract 35 46 36,
   .natural .multiply 46 38 38,.natural .add 35 38 37]

def rowPointerValues (values : ℕ → Cell) (base k row column : ℕ) : ℕ → Cell :=
  let a:=Function.update values 46 (.natural 1)
  let b:=Function.update a 35 (.natural (row-1))
  let c:=Function.update b 38 (.natural (k+1))
  let d:=Function.update c 35 (.natural ((row-1)*(k+1)))
  let e:=Function.update d 35 (.natural ((row-1)*(k+1)+column))
  let f:=Function.update e 46 (.natural 6)
  let g:=Function.update f 35 (.natural (6*((row-1)*(k+1)+column)))
  let h:=Function.update g 46 (.natural 48)
  let i:=Function.update h 35 (.natural (48+6*((row-1)*(k+1)+column)))
  let j:=Function.update i 35 (.natural (cellBase base k (row-1) column))
  let l:=Function.update j 46 (.natural 6)
  let m:=Function.update l 36 (.natural (cellBase base k (row-1) column-6))
  let o:=Function.update m 38 (.natural (6*(k+1)))
  Function.update o 37 (.natural (cellBase base k (row-1) column+6*(k+1)))

theorem rowPointerCommands_valid : ∀ command ∈ rowPointerCommands,command.Valid := by
  intro command member
  simp only [rowPointerCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst command <;>
    dsimp only [RuntimeCommand.Valid,HeaderCommand.Valid,headerWords] <;> decide

theorem rowPointerCommands_eval (values : ℕ → Cell) (base k row column : ℕ)
    (hb : values 47=.natural base) (hk : values 4=.natural k)
    (hr : values 19=.natural row) (hc : values 20=.natural column) :
    runtimeEval rowPointerCommands values=some (rowPointerValues values base k row column) := by
  simp [rowPointerCommands,runtimeEval,RuntimeCommand.eval,HeaderCommand.eval,Cell.nat?,NatOp.eval,
    hb,hk,hr,hc,rowPointerValues,cellBase,tableBase,headerWords,entryWords,Nat.add_assoc]

theorem nextRow_cellBase (base k row column : ℕ) (positive : 0 < row) :
    cellBase base k (row-1) column+6*(k+1)=cellBase base k row column := by
  have rowEq : row-1+1=row := Nat.sub_add_cancel positive
  calc
    _ = cellBase base k (row-1+1) column := by unfold cellBase tableBase entryWords; ring
    _ = _ := by rw [rowEq]

theorem previousTool_cellBase (base k row column : ℕ) (positive : 0 < column) :
    cellBase base k row column-6=cellBase base k row (column-1) := by
  have columnEq : column-1+1=column := Nat.sub_add_cancel positive
  have stepEq:=cellBase_succ_column base k row (column-1)
  rw [columnEq] at stepEq
  unfold entryWords at stepEq
  omega

theorem rowPointer_trace_memory (program : Program) (input : List Cell) (before : State)
    (base n k row column : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hb : values 47=.natural base) (hk : values 4=.natural k)
    (hr : values 19=.natural row) (hc : values 20=.natural column)
    (fetch : FetchesCode program before.pc (runtimeCode rowPointerCommands)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 4950 ∧ Header after base (rowPointerValues values base k row column) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(runtimeCode rowPointerCommands).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base :=
  runtimeCode_trace_memory rowPointerCommands program input before base n k values _ rowPointerCommands_valid header hbase
    (rowPointerCommands_eval values base k row column hb hk hr hc) fetch

end PDCompute.Solver
