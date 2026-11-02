module

public import Paid.PDLower_CalibrationCompute_Gates_030

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def levelGateResult (before : State) (base level M : ℕ) : State :=
  let loaded := loadSlotResult (loadSlotResult before base 5 .index) base 2 .total
  {loaded with
    pc:=loaded.pc+3
    register:=Function.update
      (Function.update loaded.register .total (.natural (M+1)))
      .flag (.natural (if level≤M+1 then 1 else 0))}

theorem levelGate_execute (input : List Cell) (before : State) (base : ℕ) (header : Header)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base) :
    linearExecute input (basicBlock .levelGate).body before =
      some (levelGateResult before base header.level header.M) := by
  have level := represented.lookup (offset:=5) (value:=.natural header.level) rfl
  have M := represented.lookup (offset:=2) (value:=.natural header.M) rfl
  simp [basicBlock,linearExecute,loadSlot,Instruction.execute,State.set,NatOp.eval,Comparison.nat,
    Cell.nat?,fresh,level.1,level.2,M.1,M.2,levelGateResult,loadSlotResult,Nat.add_assoc]
  all_goals
    funext register
    cases register <;> simp

theorem levelGate_header {before : State} {base : ℕ} {header : Header} (represented : header.At before base) :
    header.At (levelGateResult before base header.level header.M) base := represented

theorem levelGate_fresh (before : State) (base level M : ℕ) :
    (levelGateResult before base level M).register .fresh=before.register .fresh := by
  simp [levelGateResult,loadSlotResult]

end PDLower.CalibrationCompute
