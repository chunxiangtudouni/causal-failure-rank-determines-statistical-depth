module

public import Paid.PDLower_CalibrationCompute_HeaderOps_027
public import Paid.PDLower_CalibrationCompute_Segment_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem segment_branch (origin : ℕ) (label zero nonzero : Label) (input : List Cell)
    (before middle : State) (condition : Prop) [Decidable condition]
    (position : before.pc = labelAddress origin label)
    (run : linearExecute input (basicBlock label).body before = some middle)
    (control : (basicBlock label).control = .branch .flag zero nonzero)
    (flag : middle.register .flag = .natural (if condition then 1 else 0)) :
    Segment origin input before
      {middle with pc := labelAddress origin (if condition then nonzero else zero)}
      (15*((basicBlock label).body.length+1)+15) := by
  exact kernel_block_trace origin label input before middle _ position run (by
    by_cases decision : condition <;>
      simp [control,controlInstruction,Instruction.execute,flag,decision,Cell.nat?])

def sumGateResult (before : State) (base cursor level : ℕ) : State :=
  let loaded := loadSlotResult (loadSlotResult before base 7 .index) base 5 .total
  {loaded with
    pc := loaded.pc+1
    register := Function.update loaded.register .flag (.natural (if cursor < level then 1 else 0))}

theorem sumGate_execute (input : List Cell) (before : State) (base : ℕ) (header : Header)
    (represented : header.At before base) (fresh : before.register .fresh = .natural base) :
    linearExecute input (basicBlock .sumGate).body before =
      some (sumGateResult before base header.cursor header.level) := by
  have cursor := represented.lookup (offset := 7) (value := .natural header.cursor) rfl
  have level := represented.lookup (offset := 5) (value := .natural header.level) rfl
  simp [basicBlock,linearExecute,loadSlot,Instruction.execute,State.set,NatOp.eval,Comparison.nat,
    Cell.nat?,fresh,cursor.1,cursor.2,level.1,level.2,sumGateResult,loadSlotResult,Nat.add_assoc]

theorem sumGate_header {before : State} {base : ℕ} {header : Header} (represented : header.At before base) :
    header.At (sumGateResult before base header.cursor header.level) base := represented

theorem sumGate_index (before : State) (base : ℕ) (header : Header) (represented : header.At before base) :
    (sumGateResult before base header.cursor header.level).register .index = .natural header.cursor := by
  have cursor := represented.lookup (offset := 7) (value := .natural header.cursor) rfl
  simpa [sumGateResult,loadSlotResult] using cursor.1

theorem sumGate_fresh (before : State) (base cursor level : ℕ) :
    (sumGateResult before base cursor level).register .fresh = before.register .fresh := by
  simp [sumGateResult,loadSlotResult]

end PDLower.CalibrationCompute
