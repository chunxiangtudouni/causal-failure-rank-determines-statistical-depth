module

public import Paid.PDROC_CalibrationRow_InitOperands_002
public import Paid.PDROC_CalibrationRow_OperandPrefix_004
public import Paid.PDROC_CalibrationRow_Init_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- Same budget over the entire original thirteen-op initStore body,
including the real row write before the later header7 increment. -/
theorem initStore_prefix_safe (input : List Cell) (before : State)
    (base cursor budget : ℕ) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base)
    (readLive : base+9∈before.live) (read : before.heap (base+9)=.natural (firstRow base))
    (cursorLive : base+7∈before.live) (cursorValue : before.heap (base+7)=.natural cursor)
    (index : before.register .index=.natural cursor)
    (readSlotBits : 1+natBits (base+9)≤budget) (cursorSlotBits : 1+natBits (base+7)≤budget)
    (targetBits : (Cell.natural (firstRow base+cursor)).bits≤budget)
    (oneBits : (Cell.natural 1).bits≤budget) (nextBits : (Cell.natural (cursor+1)).bits≤budget)
    (pcBits : natBits (before.pc+13)≤budget) :
    PrefixSafe input (basicBlock .initStore).body before budget := by
  let middle := initStoreLeadResult before base cursor
  have firstRun : linearExecute input initStoreLeadCode before=some middle :=
    initStoreLead_execute input before base cursor fresh readLive read index
  have firstSafe := initStoreLead_prefix_safe input before base cursor budget safe fresh readLive read index
    readSlotBits targetBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+5≤before.pc+13)).trans pcBits)
  have fields := initStoreLead_fields before base cursor
  have middleFresh : middle.register .fresh=.natural base := fields.2.2.1.trans fresh
  have middleLive : base+7∈middle.live := by
    rw [show middle.live=insert (firstRow base+cursor) before.live from fields.2.1]
    exact Finset.mem_insert_of_mem cursorLive
  have middleCursor : middle.heap (base+7)=.natural cursor := by
    rw [show middle.heap=Function.update before.heap (firstRow base+cursor) (before.register .value) from fields.1]
    rw [Function.update_of_ne (by unfold firstRow; omega : base+7≠firstRow base+cursor)]
    exact cursorValue
  have laterSafe := increment_prefix_safe input middle base 7 cursor budget (firstSafe.final firstRun)
    middleFresh middleLive middleCursor cursorSlotBits oneBits nextBits
    (by simpa only [middle,initStoreLeadResult,loadSlotResult,State.set,writeCell,Nat.add_assoc] using pcBits)
  rw [initStore_body]
  exact PrefixSafe.append input initStoreLeadCode (incrementSlot 7) before middle budget firstRun firstSafe laterSafe

end PDROC.CalibrationRow.Operand
