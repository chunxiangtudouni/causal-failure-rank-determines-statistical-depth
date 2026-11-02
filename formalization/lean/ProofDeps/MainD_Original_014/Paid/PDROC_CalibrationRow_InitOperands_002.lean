module

public import Paid.PDROC_CalibrationRow_OperandPrefix_002
public import Paid.PDROC_CalibrationRow_Init_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- Real load-pointer/add-address/store prefixes. The new row location
may initially be unallocated; its inserted Cell is the already bounded
actual caller value. No value is read from that old row location. -/
theorem initStoreLead_prefix_safe (input : List Cell) (before : State)
    (base cursor budget : ℕ) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base) (live : base+9∈before.live)
    (read : before.heap (base+9)=.natural (firstRow base))
    (index : before.register .index=.natural cursor)
    (slotBits : 1+natBits (base+9)≤budget)
    (addressBits : (Cell.natural (firstRow base+cursor)).bits≤budget)
    (pcBits : natBits (before.pc+5)≤budget) :
    PrefixSafe input initStoreLeadCode before budget := by
  let loaded := loadSlotResult before base 9 .old
  let addressed := ({loaded with pc:=loaded.pc+1}).set .address (.natural (firstRow base+cursor))
  have loadRun : linearExecute input (loadSlot 9 .old) before=some loaded :=
    loadSlot_execute input before base 9 .old fresh live
  have loadSafe := PrefixSafe.loadSlot input before base 9 budget .old safe fresh live slotBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+3≤before.pc+5)).trans pcBits)
  have addRun : linearExecute input [.natOp .add .address .old .index] loaded=some addressed := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,loaded,loadSlotResult,read,index,addressed]
  have addSafe := PrefixSafe.natOp input loaded budget .add .address .old .index
    (firstRow base) cursor (firstRow base+cursor) (loadSafe.final loadRun)
    (by simp [loaded,loadSlotResult,read]) (by simp [loaded,loadSlotResult,index]) rfl addressBits
    (by simpa only [loaded,loadSlotResult,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+5)).trans pcBits))
  have storeSafe := PrefixSafe.store input addressed budget .address .value (firstRow base+cursor)
    (addSafe.final addRun) (by simp [addressed,State.set])
    (by simpa only [addressed,loaded,loadSlotResult,State.set,Nat.add_assoc] using pcBits)
  have suffix := PrefixSafe.append input [.natOp .add .address .old .index] [.store .address .value]
    loaded addressed budget addRun addSafe storeSafe
  exact PrefixSafe.append input (loadSlot 9 .old) [.natOp .add .address .old .index,.store .address .value]
    before loaded budget loadRun loadSafe suffix

end PDROC.CalibrationRow.Operand
