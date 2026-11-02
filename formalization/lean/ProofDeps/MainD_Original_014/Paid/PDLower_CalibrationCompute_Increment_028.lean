module

public import Paid.PDLower_CalibrationCompute_HeaderOps_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def incrementSlotLoaded (before : State) (base offset value : ℕ) : State :=
  let loaded := loadSlotResult before base offset .index
  {loaded with
    pc := loaded.pc+2
    register := Function.update (Function.update loaded.register .flag (.natural 1))
      .index (.natural (value+1))}

def incrementSlotResult (before : State) (base offset value : ℕ) : State :=
  storeSlotResult (incrementSlotLoaded before base offset value) base offset .index

theorem incrementSlot_execute (input : List Cell) (before : State) (base offset value : ℕ)
    (fresh : before.register .fresh = .natural base)
    (live : base+offset ∈ before.live) (correct : before.heap (base+offset) = .natural value) :
    linearExecute input (incrementSlot offset) before = some (incrementSlotResult before base offset value) := by
  simp only [incrementSlot,List.append_assoc,linearExecute_append]
  rw [loadSlot_execute input before base offset .index fresh live,Option.bind_some]
  have two : linearExecute input [.constant .flag (.natural 1),.natOp .add .index .index .flag]
      (loadSlotResult before base offset .index) = some (incrementSlotLoaded before base offset value) := by
    simp [linearExecute,Instruction.execute,State.set,loadSlotResult,correct,Cell.nat?,NatOp.eval,incrementSlotLoaded,Nat.add_assoc]
  rw [two,Option.bind_some]
  exact storeSlot_execute input _ base offset .index (by simpa [incrementSlotLoaded,loadSlotResult] using fresh) (by decide)

theorem incrementSlot_pc (before : State) (base offset value : ℕ) :
    (incrementSlotResult before base offset value).pc = before.pc+8 := by
  simp [incrementSlotResult,incrementSlotLoaded,loadSlotResult,storeSlotResult,Nat.add_assoc]

theorem incrementSlot_fresh (before : State) (base offset value : ℕ) :
    (incrementSlotResult before base offset value).register .fresh = before.register .fresh := by
  simp [incrementSlotResult,incrementSlotLoaded,loadSlotResult,storeSlotResult]

theorem incrementSlot_output (before : State) (base offset value : ℕ) :
    (incrementSlotResult before base offset value).output = before.output := rfl

theorem incrementSlot_header {header updated : Header} {before : State} {base offset value : ℕ}
    (represented : header.At before base) (inside : offset < 16)
    (updatedCells : header.cells.set offset (.natural (value+1)) = updated.cells) :
    updated.At (incrementSlotResult before base offset value) base := by
  have unchanged : header.At (incrementSlotLoaded before base offset value) base := represented
  exact unchanged.storeResult offset inside .index (.natural (value+1)) (by simp [incrementSlotLoaded]) updatedCells

end PDLower.CalibrationCompute
