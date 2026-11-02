module

public import Paid.PDROC_CalibrationRow_ControlOperands_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- Six genuine zeroWrite instructions. The old destination cell is
never read: its new address and Rat0 are intrinsically bounded, while
every other old caller cell keeps the SAME B. -/
theorem zeroWrite_prefix_safe (input : List Cell) (before : State) (base write cursor budget : ℕ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (live : base+10∈before.live) (pointer : before.heap (base+10)=.natural write)
    (index : before.register .index=.natural cursor)
    (headerBits : 1+natBits (base+10)≤budget)
    (targetBits : (Cell.natural (write+cursor)).bits≤budget)
    (zeroBits : (Cell.rational 0).bits≤budget) (pcBits : natBits (before.pc+6)≤budget) :
    PrefixSafe input zeroWriteCode before budget := by
  let loaded := loadSlotResult before base 10 .old
  let addressed := ({loaded with pc:=loaded.pc+1}).set .address (.natural (write+cursor))
  let zeroed := ({addressed with pc:=addressed.pc+1}).set .value (.rational 0)
  have loadRun : linearExecute input (loadSlot 10 .old) before=some loaded :=
    loadSlot_execute input before base 10 .old fresh live
  have loadSafe := PrefixSafe.loadSlot input before base 10 budget .old safe fresh live headerBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+3≤before.pc+6)).trans pcBits)
  have addRun : linearExecute input [.natOp .add .address .old .index] loaded=some addressed := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,loaded,loadSlotResult,pointer,index,addressed]
  have addSafe := PrefixSafe.natOp input loaded budget .add .address .old .index write cursor (write+cursor)
    (loadSafe.final loadRun) (by simp [loaded,loadSlotResult,pointer]) (by simp [loaded,loadSlotResult,index])
    rfl targetBits (by simpa only [loaded,loadSlotResult,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+6)).trans pcBits))
  have zeroRun : linearExecute input [.constant .value (.rational 0)] addressed=some zeroed := rfl
  have zeroSafe := PrefixSafe.constant input addressed budget .value (.rational 0)
    (addSafe.final addRun) zeroBits
    (by simpa only [addressed,loaded,loadSlotResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+5≤before.pc+6)).trans pcBits))
  have storeSafe := PrefixSafe.store input zeroed budget .address .value (write+cursor)
    (zeroSafe.final zeroRun) (by simp [zeroed,addressed,State.set])
    (by simpa only [zeroed,addressed,loaded,loadSlotResult,State.set,Nat.add_assoc] using pcBits)
  have suffix := PrefixSafe.append input [.constant .value (.rational 0)] [.store .address .value]
    addressed zeroed budget zeroRun zeroSafe storeSafe
  have tail := PrefixSafe.append input [.natOp .add .address .old .index]
    ([.constant .value (.rational 0)]++[.store .address .value]) loaded addressed budget addRun addSafe suffix
  change PrefixSafe input (loadSlot 10 .old++
    ([.natOp .add .address .old .index]++([.constant .value (.rational 0)]++[.store .address .value]))) before budget
  exact PrefixSafe.append input (loadSlot 10 .old)
    ([.natOp .add .address .old .index]++([.constant .value (.rational 0)]++[.store .address .value]))
    before loaded budget loadRun loadSafe tail

end PDROC.CalibrationRow.Operand
