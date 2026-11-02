module

public import Paid.PDROC_CalibrationRow_004
public import Paid.PDROC_CalibrationRow_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

def initCellResult (before : State) (base level cursor : ℕ) : State :=
  let loaded := loadSlotResult before base 5 .total
  let compared := ({loaded with pc:=loaded.pc+1}).set .flag
    (.natural (if cursor=level then 1 else 0))
  ({compared with pc:=compared.pc+1}).set .value (.rational 0)

theorem initCell_execute (input : List Cell) (before : State) (base level cursor : ℕ)
    (fresh : before.register .fresh=.natural base)
    (live : base+5 ∈ before.live) (levelValue : before.heap (base+5)=.natural level)
    (index : before.register .index=.natural cursor) :
    linearExecute input (basicBlock .initCell).body before=some (initCellResult before base level cursor) := by
  simp [basicBlock,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Comparison.nat,
    Cell.nat?,fresh,live,levelValue,index,initCellResult,loadSlotResult,Nat.add_assoc]

theorem initCell_fields (before : State) (base level cursor : ℕ) :
    (initCellResult before base level cursor).heap=before.heap ∧
    (initCellResult before base level cursor).live=before.live ∧
    (initCellResult before base level cursor).register .fresh=before.register .fresh ∧
    (initCellResult before base level cursor).register .index=before.register .index ∧
    (initCellResult before base level cursor).register .flag=.natural (if cursor=level then 1 else 0) ∧
    (initCellResult before base level cursor).register .value=.rational 0 ∧
    (initCellResult before base level cursor).pc=before.pc+5 ∧
    (initCellResult before base level cursor).output=before.output := by
  simp [initCellResult,loadSlotResult,State.set,Nat.add_assoc]

def initCenterResult (before : State) : State :=
  ({before with pc:=before.pc+1}).set .value (.rational 1)

theorem initCenter_execute (input : List Cell) (before : State) :
    linearExecute input (basicBlock .initCenter).body before=some (initCenterResult before) := by
  simp [basicBlock,linearExecute,Instruction.execute,initCenterResult]

theorem initCenter_fields (before : State) :
    (initCenterResult before).heap=before.heap ∧ (initCenterResult before).live=before.live ∧
    (initCenterResult before).register .fresh=before.register .fresh ∧
    (initCenterResult before).register .index=before.register .index ∧
    (initCenterResult before).register .value=.rational 1 ∧
    (initCenterResult before).pc=before.pc+1 ∧ (initCenterResult before).output=before.output := by
  simp [initCenterResult,State.set]

/-- The five literal instructions before initStore increments header7.
They never read the initially uninitialized row cell. -/
def initStoreLeadCode : List Instruction :=
  loadSlot 9 .old ++ [.natOp .add .address .old .index,.store .address .value]

def initStoreLeadResult (before : State) (base cursor : ℕ) : State :=
  let loaded := loadSlotResult before base 9 .old
  let addressed := ({loaded with pc:=loaded.pc+1}).set .address (.natural (firstRow base+cursor))
  writeCell addressed (firstRow base+cursor) (before.register .value)

theorem initStoreLead_execute (input : List Cell) (before : State) (base cursor : ℕ)
    (fresh : before.register .fresh=.natural base)
    (live : base+9 ∈ before.live) (read : before.heap (base+9)=.natural (firstRow base))
    (index : before.register .index=.natural cursor) :
    linearExecute input initStoreLeadCode before=some (initStoreLeadResult before base cursor) := by
  simp [initStoreLeadCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,
    Cell.nat?,fresh,live,read,index,initStoreLeadResult,loadSlotResult,writeCell,Nat.add_assoc]

theorem initStoreLead_fields (before : State) (base cursor : ℕ) :
    (initStoreLeadResult before base cursor).heap=
      Function.update before.heap (firstRow base+cursor) (before.register .value) ∧
    (initStoreLeadResult before base cursor).live=insert (firstRow base+cursor) before.live ∧
    (initStoreLeadResult before base cursor).register .fresh=before.register .fresh ∧
    (initStoreLeadResult before base cursor).register .index=before.register .index ∧
    (initStoreLeadResult before base cursor).pc=before.pc+5 ∧
    (initStoreLeadResult before base cursor).output=before.output := by
  simp [initStoreLeadResult,loadSlotResult,writeCell,State.set,Nat.add_assoc]

theorem initStoreLead_frame (before : State) (base M cursor : ℕ)
    (inside : cursor<rowWidth M) :
    MemoryFrame (region base M) before (initStoreLeadResult before base cursor) := by
  have fields := initStoreLead_fields before base cursor
  exact frame_of_one_update (region base M) before _ (firstRow base+cursor) (before.register .value)
    (first_mem_region base M cursor inside) fields.1 fields.2.1

theorem initStoreLead_delta_prefix (P : Parameters) (before : State) (base level cursor : ℕ)
    (inside : cursor<2*level+1)
    (prefixRow : RowPrefix before (firstRow base) (P.walkRow level true 0) cursor)
    (source : before.register .value=.rational (if cursor=level then 1 else 0)) :
    RowPrefix (initStoreLeadResult before base cursor) (firstRow base) (P.walkRow level true 0) (cursor+1) := by
  have stored := original_center_write P level cursor before (firstRow base) inside prefixRow
  have fields := initStoreLead_fields before base cursor
  apply RowPrefix.transport (writeCell before (firstRow base+cursor) (.rational (if cursor=level then 1 else 0)))
    (initStoreLeadResult before base cursor) (firstRow base) (P.walkRow level true 0) (cursor+1) stored
  · rw [fields.2.1]
    exact fun _ member => member
  · intro i bound
    rw [fields.1,source]
    rfl

end PDROC.CalibrationRow
