module

public import Paid.PDROC_CalibrationRow_ControlOperands_002
public import Paid.PDROC_CalibrationRow_OperandPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- All TWENTY original stepNext prefixes retain caller B, using the
proved original increment8 followed by both loads and both stores.
The temporary pointer alias is a real state covered by this same bound. -/
theorem stepNext_prefix_safe (input : List Cell) (before : State) (base clock budget : ℕ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (clockLive : base+6∈before.live) (clockValue : before.heap (base+6)=.natural clock)
    (readLive : base+9∈before.live) (writeLive : base+10∈before.live)
    (clockBits : 1+natBits (base+6)≤budget) (readBits : 1+natBits (base+9)≤budget)
    (writeBits : 1+natBits (base+10)≤budget) (oneBits : (Cell.natural 1).bits≤budget)
    (nextBits : (Cell.natural (clock+1)).bits≤budget) (pcBits : natBits (before.pc+20)≤budget) :
    PrefixSafe input (basicBlock .stepNext).body before budget := by
  let incremented := incrementSlotResult before base 6 clock
  have incRun : linearExecute input (incrementSlot 6) before=some incremented :=
    incrementSlot_execute input before base 6 clock fresh clockLive clockValue
  have incSafe := increment_prefix_safe input before base 6 clock budget safe fresh clockLive clockValue
    clockBits oneBits nextBits ((PDROC.DataBits.natBits_mono (by omega : before.pc+8≤before.pc+20)).trans pcBits)
  have incFresh := (incrementSlot_fresh before base 6 clock).trans fresh
  have tailSafe := swapTail_prefix_safe input incremented base budget (incSafe.final incRun) incFresh
    (Finset.mem_insert_of_mem readLive) (Finset.mem_insert_of_mem writeLive) readBits writeBits
    (by simpa only [incremented,incrementSlot_pc,Nat.add_assoc] using pcBits)
  have code : (basicBlock .stepNext).body=incrementSlot 6++swapTailCode := rfl
  rw [code]
  exact PrefixSafe.append input (incrementSlot 6) swapTailCode before incremented budget incRun incSafe tailSafe

end PDROC.CalibrationRow.Operand
