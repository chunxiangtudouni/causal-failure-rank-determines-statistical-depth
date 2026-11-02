module

public import Paid.PDLower_CalibrationCompute_HeaderOps_027
public import Paid.PDLower_CalibrationCompute_Segment_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def finishResult (before : State) (base M : ℕ) : State :=
  let loaded := loadSlotResult (loadSlotResult before base 0 .old) base 2 .index
  {loaded with
    pc:=loaded.pc+9
    register:=Function.update
      (Function.update
        (Function.update
          (Function.update loaded.register .flag (.natural 16))
          .index (.natural (rowWidth M)))
        .value (.natural (16+2*rowWidth M)))
      .address (.natural (resultBase base M))}

theorem finish_execute (input : List Cell) (before : State) (base : ℕ) (header : Header)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base) :
    linearExecute input (basicBlock .finish).body before = some (finishResult before base header.M) := by
  have ret := represented.lookup (offset:=0) (value:=.natural header.returnPC) rfl
  simp only [Nat.add_zero] at ret
  have M := represented.lookup (offset:=2) (value:=.natural header.M) rfl
  simp [basicBlock,linearExecute,loadSlot,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    fresh,ret.1,ret.2,M.1,M.2,finishResult,loadSlotResult,rowWidth,resultBase,Nat.add_assoc,mul_two,two_mul]
  all_goals
    funext register
    cases register <;> simp <;> omega

theorem finish_return (origin : ℕ) (input : List Cell) (before : State) (base : ℕ) (header : Header)
    (position : before.pc=labelAddress origin .finish)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base) :
    Segment origin input before {finishResult before base header.M with pc:=header.returnPC} 255 := by
  have ret := represented.lookup (offset:=0) (value:=.natural header.returnPC) rfl
  simp only [Nat.add_zero] at ret
  exact kernel_block_trace origin .finish input before (finishResult before base header.M) _ position
    (finish_execute input before base header represented fresh) (by
      simp [basicBlock,controlInstruction,Instruction.execute,finishResult,loadSlotResult,ret.1,Cell.nat?])

theorem finish_registers (before : State) (base : ℕ) (header : Header)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base) :
    (finishResult before base header.M).register .old=.natural header.returnPC ∧
    (finishResult before base header.M).register .fresh=.natural base ∧
    (finishResult before base header.M).register .address=.natural (resultBase base header.M) ∧
    (finishResult before base header.M).register .index=.natural (rowWidth header.M) := by
  have ret := represented.lookup (offset:=0) (value:=.natural header.returnPC) rfl
  simp only [Nat.add_zero] at ret
  simp [finishResult,loadSlotResult,ret.1,fresh]

end PDLower.CalibrationCompute
