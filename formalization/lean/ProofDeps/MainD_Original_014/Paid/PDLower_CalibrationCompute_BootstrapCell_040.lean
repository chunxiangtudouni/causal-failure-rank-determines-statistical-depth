module

public import Paid.PDLower_CalibrationCompute_Bootstrap_015
public import Paid.PDLower_CalibrationCompute_Linear_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def bootstrapCopyBody : List Instruction :=
  [.loadInput .fresh .old,.store .address .fresh,.constant .fresh (.natural 1),
   .natOp .add .old .old .fresh,.natOp .add .address .address .fresh,
   .natOp .subtract .flag .flag .fresh]

def bootstrapCopyResult (before : State) (source destination remaining : ℕ) (value : Cell) : State :=
  {before with
    pc:=before.pc+6
    register:=Function.update
      (Function.update
        (Function.update
          (Function.update before.register .fresh (.natural 1))
          .old (.natural (source+1)))
        .address (.natural (destination+1)))
      .flag (.natural (remaining-1)),
    heap:=Function.update before.heap destination value,
    live:=insert destination before.live}

theorem bootstrapCopy_execute (input : List Cell) (before : State) (source destination remaining : ℕ) (value : Cell)
    (old : before.register .old=.natural source) (address : before.register .address=.natural destination)
    (flag : before.register .flag=.natural remaining) (data : input[source]?=some value) :
    linearExecute input bootstrapCopyBody before = some (bootstrapCopyResult before source destination remaining value) := by
  simp [bootstrapCopyBody,linearExecute,Instruction.execute,State.set,Cell.nat?,NatOp.eval,old,address,flag,data,
    bootstrapCopyResult,Nat.add_assoc]

theorem bootstrapCopy_fetch (origin offset : ℕ) (inside : offset<bootstrapCopyBody.length) :
    (bootstrap origin)[13+offset]?=bootstrapCopyBody[offset]? := by
  have alternatives : offset=0 ∨ offset=1 ∨ offset=2 ∨ offset=3 ∨ offset=4 ∨ offset=5 := by
    change offset<6 at inside
    omega
  rcases alternatives with eq|eq|eq|eq|eq|eq <;> subst offset <;> rfl

theorem calibrate_bootstrapCopy_fetch (offset : ℕ) (inside : offset<bootstrapCopyBody.length) :
    calibrate[mainStart+13+offset]?=bootstrapCopyBody[offset]? := by
  rw [Nat.add_assoc,calibrate_bootstrap_fetch]
  exact bootstrapCopy_fetch mainStart offset inside

theorem bootstrapCopy_output (before : State) (source destination remaining : ℕ) (value : Cell) :
    (bootstrapCopyResult before source destination remaining value).output=before.output := rfl

end PDLower.CalibrationCompute
