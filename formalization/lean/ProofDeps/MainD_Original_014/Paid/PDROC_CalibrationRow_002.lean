module

public import Paid.PDROC_CalibrationRow_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- The first ten actual instructions of original levelInit. -/
def widthCode : List Instruction :=
  loadSlot 5 .index ++
    [.constant .flag (.natural 2),.natOp .multiply .index .index .flag,
      .constant .flag (.natural 1),.natOp .add .index .index .flag] ++ storeSlot 8 .index

/-- The remaining literal twenty instructions reset both true row
addresses and cursor; they do not read incoming row contents or clock. -/
def buffersCode : List Instruction :=
  [.constant .old (.natural 16),.natOp .add .old .fresh .old] ++ storeSlot 9 .old ++
    loadSlot 2 .index ++
    [.constant .flag (.natural 2),.natOp .multiply .index .index .flag,
      .constant .flag (.natural 3),.natOp .add .index .index .flag,
      .natOp .add .total .old .index] ++ storeSlot 10 .total ++ constantSlot 7 (.natural 0)

theorem levelInit_decompose : (basicBlock Label.levelInit).body=widthCode++buffersCode := rfl

def widthResult (before : State) (base level : ℕ) : State :=
  let loaded := loadSlotResult before base 5 .index
  let two := ({loaded with pc:=loaded.pc+1}).set .flag (.natural 2)
  let doubled := ({two with pc:=two.pc+1}).set .index (.natural (level*2))
  let one := ({doubled with pc:=doubled.pc+1}).set .flag (.natural 1)
  let computed := ({one with pc:=one.pc+1}).set .index (.natural (level*2+1))
  storeSlotResult computed base 8 .index

theorem width_execute (input : List Cell) (before : State) (base level : ℕ)
    (fresh : before.register .fresh=.natural base)
    (live : base+5 ∈ before.live) (value : before.heap (base+5)=.natural level) :
    linearExecute input widthCode before=some (widthResult before base level) := by
  simp [widthCode,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,
    Cell.nat?,fresh,live,value,widthResult,loadSlotResult,storeSlotResult,Nat.add_assoc]

theorem widthResult_fields (before : State) (base level : ℕ) :
    (widthResult before base level).heap=Function.update before.heap (base+8) (.natural (2*level+1)) ∧
    (widthResult before base level).live=insert (base+8) before.live ∧
    (widthResult before base level).register .fresh=before.register .fresh ∧
    (widthResult before base level).register .old=before.register .old ∧
    (widthResult before base level).pc=before.pc+10 ∧
    (widthResult before base level).output=before.output := by
  simp [widthResult,loadSlotResult,storeSlotResult,State.set,Nat.mul_comm]

theorem widthResult_frame (before : State) (base level M : ℕ) :
    MemoryFrame (region base M) before (widthResult before base level) := by
  have fields := widthResult_fields before base level
  have inside := header_mem_region base M 8 (by decide) (by decide)
  have different (address : ℕ) (outside : address ∉ region base M) : address ≠ base+8 := by
    intro equal
    exact outside (equal.symm ▸ inside)
  constructor
  · intro address outside
    rw [fields.1]
    exact Function.update_of_ne (different address outside) _ _
  · intro address outside
    rw [fields.2.1]
    simp only [Finset.mem_insert,different address outside,false_or]

/-- This phase has no width/clock/row oracle: it reads only actual header5. -/
theorem header_width_execute (input : List Cell) (P : Parameters) (before : State) (base level : ℕ)
    (header : Header P base level before) :
    linearExecute input widthCode before=some (widthResult before base level) ∧
      MemoryFrame (region base P.certificate.M) before (widthResult before base level) :=
  ⟨width_execute input before base level header.fresh (header.live 5 (by decide)) header.level,
    widthResult_frame before base level P.certificate.M⟩

end PDROC.CalibrationRow
