module

public import Paid.PDROC_CalibrationRow_OperandPrefix_002
public import Paid.PDLower_CalibrationCompute_Increment_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- The actual eight-opcode header increment retains caller B throughout.
Only the actual successor Cell/address/PC need intrinsic bounds; unchanged
caller registers and old live heap values never gain a width-dependent factor. -/
theorem increment_prefix_safe (input : List Cell) (before : State)
    (base offset value budget : ℕ) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base) (live : base+offset∈before.live)
    (cell : before.heap (base+offset)=.natural value)
    (addressBits : 1+natBits (base+offset)≤budget)
    (oneBits : (Cell.natural 1).bits≤budget) (nextBits : (Cell.natural (value+1)).bits≤budget)
    (pcBits : natBits (before.pc+8)≤budget) :
    PrefixSafe input (incrementSlot offset) before budget := by
  let loaded := loadSlotResult before base offset .index
  let one := ({loaded with pc:=loaded.pc+1}).set .flag (.natural 1)
  let added := ({one with pc:=one.pc+1}).set .index (.natural (value+1))
  have loadRun : linearExecute input (loadSlot offset .index) before=some loaded :=
    loadSlot_execute input before base offset .index fresh live
  have loadSafe := PrefixSafe.loadSlot input before base offset budget .index safe fresh live addressBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+3≤before.pc+8)).trans pcBits)
  have oneRun : linearExecute input [.constant .flag (.natural 1)] loaded=some one := rfl
  have oneSafe := PrefixSafe.constant input loaded budget .flag (.natural 1) (loadSafe.final loadRun) oneBits
    (by simpa only [loaded,loadSlotResult,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+8)).trans pcBits))
  have addRun : linearExecute input [.natOp .add .index .index .flag] one=some added := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,one,loaded,loadSlotResult,State.set,cell,added]
  have addSafe := PrefixSafe.natOp input one budget .add .index .index .flag value 1 (value+1)
    (oneSafe.final oneRun) (by simp [one,loaded,loadSlotResult,State.set,cell])
    (by simp [one,State.set]) rfl nextBits
    (by simpa only [one,loaded,loadSlotResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+5≤before.pc+8)).trans pcBits))
  have addedFresh : added.register .fresh=.natural base := by
    simp [added,one,loaded,loadSlotResult,State.set,fresh]
  have storeSafe := PrefixSafe.storeSlot input added base offset budget .index (addSafe.final addRun)
    addedFresh (by decide) addressBits
    (by simpa only [added,one,loaded,loadSlotResult,State.set,Nat.add_assoc] using pcBits)
  have tailSafe := PrefixSafe.append input [.natOp .add .index .index .flag] (storeSlot offset .index)
    one added budget addRun addSafe storeSafe
  have middleSafe := PrefixSafe.append input [.constant .flag (.natural 1)]
    ([.natOp .add .index .index .flag]++storeSlot offset .index) loaded one budget oneRun oneSafe tailSafe
  change PrefixSafe input (loadSlot offset .index++
    ([.constant .flag (.natural 1)]++([.natOp .add .index .index .flag]++storeSlot offset .index))) before budget
  exact PrefixSafe.append input (loadSlot offset .index)
    ([.constant .flag (.natural 1)]++([.natOp .add .index .index .flag]++storeSlot offset .index))
    before loaded budget loadRun loadSafe middleSafe

end PDROC.CalibrationRow.Operand
