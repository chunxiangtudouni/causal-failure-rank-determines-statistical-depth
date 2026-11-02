module

public import Paid.PDROC_CalibrationRow_ControlOperands_004
public import Paid.PDROC_CalibrationRow_OperandPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- Six real zero stores/address instructions followed by the original
eight-op cursor increment. Prefix6 has already written Rat0, but only
prefix14 stores header7=c+1; BOTH phases keep the same caller budget. -/
theorem zeroCell_prefix_safe (input : List Cell) (P : Parameters)
    (origin base level clock cursor read write budget : ℕ) (previous : Array ℚ) (before : State)
    (data : ZeroData P base level clock cursor read write previous before)
    (position : before.pc=labelAddress origin .zeroCell) (index : before.register .index=.natural cursor)
    (inside : cursor<2*level+1) (levelBound : level≤P.certificate.M+1)
    (safe : SafeBits before budget) (bounds : ControlBudget P origin base budget) :
    PrefixSafe input (basicBlock .zeroCell).body before budget := by
  have active := activeWidth_le P.certificate.M level levelBound
  have cursorBound : cursor≤rowWidth P.certificate.M := by omega
  have nextBound : cursor+1≤controlNaturalCap P base := by
    have cap := (controlNaturalCap_lower P base).2.1
    omega
  have targetBits : (Cell.natural (write+cursor)).bits≤budget :=
    (ControlBudget.rowAddress P origin base budget read write cursor bounds data.buffers cursorBound).2
  have zeroBits : (Cell.rational 0).bits≤budget :=
    (show (Cell.rational 0).bits≤4 by decide).trans bounds.small
  let stored := zeroWriteResult before base write cursor
  have zeroRun : linearExecute input zeroWriteCode before=some stored :=
    zeroWrite_execute input before base write cursor data.header.fresh (data.header.live 10 (by decide)) data.writeValue index
  have zeroSafe := zeroWrite_prefix_safe input before base write cursor budget safe data.header.fresh
    (data.header.live 10 (by decide)) data.writeValue index
    (ControlBudget.slot P origin base budget 10 bounds (by decide)) targetBits zeroBits
    (ControlBudget.pc_prefix P origin base budget bounds before .zeroCell 6 position (by decide))
  have fields := zeroWrite_fields before base write cursor
  have storedPC : stored.pc=before.pc+6 := fields.2.2.2.2.1
  have fresh := fields.2.2.1.trans data.header.fresh
  have live : base+7∈stored.live := by
    rw [fields.2.1]
    exact Finset.mem_insert_of_mem (data.header.live 7 (by decide))
  have cursorValue : stored.heap (base+7)=.natural cursor := by
    rw [fields.1,Function.update_of_ne (Ne.symm (Buffers.write_header_ne base P.certificate.M read write cursor 7 data.buffers (by decide)))]
    exact data.cursorValue
  have incSafe := increment_prefix_safe input stored base 7 cursor budget (zeroSafe.final zeroRun) fresh live cursorValue
    (ControlBudget.slot P origin base budget 7 bounds (by decide))
    (ControlBudget.literal P origin base budget 1 bounds (by decide))
    (ControlBudget.nat P origin base budget (cursor+1) bounds nextBound)
    (by simpa only [storedPC,Nat.add_assoc] using
      ControlBudget.pc_prefix P origin base budget bounds before .zeroCell 14 position (by decide))
  rw [zeroCell_decompose]
  exact PrefixSafe.append input zeroWriteCode (incrementSlot 7) before stored budget zeroRun zeroSafe incSafe

end PDROC.CalibrationRow.Operand
