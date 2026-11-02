module

public import Paid.PDROC_CalibrationRow_ControlOperands_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- Actual width computation: load L, multiply by2, add1, store header8.
Each newly computed natural is bounded once intrinsically; unchanged
caller cells retain exactly the same budget through all ten prefixes. -/
theorem width_prefix_safe (input : List Cell) (before : State) (base level budget : ℕ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (live : base+5∈before.live) (levelValue : before.heap (base+5)=.natural level)
    (fiveBits : 1+natBits (base+5)≤budget) (eightBits : 1+natBits (base+8)≤budget)
    (twoBits : (Cell.natural 2).bits≤budget) (oneBits : (Cell.natural 1).bits≤budget)
    (doubleBits : (Cell.natural (level*2)).bits≤budget)
    (widthBits : (Cell.natural (level*2+1)).bits≤budget)
    (pcBits : natBits (before.pc+10)≤budget) :
    PrefixSafe input widthCode before budget := by
  let loaded := loadSlotResult before base 5 .index
  let two := ({loaded with pc:=loaded.pc+1}).set .flag (.natural 2)
  let doubled := ({two with pc:=two.pc+1}).set .index (.natural (level*2))
  let one := ({doubled with pc:=doubled.pc+1}).set .flag (.natural 1)
  let added := ({one with pc:=one.pc+1}).set .index (.natural (level*2+1))
  have loadRun : linearExecute input (loadSlot 5 .index) before=some loaded :=
    loadSlot_execute input before base 5 .index fresh live
  have loadSafe := PrefixSafe.loadSlot input before base 5 budget .index safe fresh live fiveBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+3≤before.pc+10)).trans pcBits)
  have twoRun : linearExecute input [.constant .flag (.natural 2)] loaded=some two := rfl
  have twoSafe := PrefixSafe.constant input loaded budget .flag (.natural 2) (loadSafe.final loadRun) twoBits
    (by simpa only [loaded,loadSlotResult,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+10)).trans pcBits))
  have doubleRun : linearExecute input [.natOp .multiply .index .index .flag] two=some doubled := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,two,loaded,loadSlotResult,State.set,levelValue,doubled]
  have doubleSafe := PrefixSafe.natOp input two budget .multiply .index .index .flag level 2 (level*2)
    (twoSafe.final twoRun) (by simp [two,loaded,loadSlotResult,State.set,levelValue])
    (by simp [two,State.set]) rfl doubleBits
    (by simpa only [two,loaded,loadSlotResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+5≤before.pc+10)).trans pcBits))
  have oneRun : linearExecute input [.constant .flag (.natural 1)] doubled=some one := rfl
  have oneSafe := PrefixSafe.constant input doubled budget .flag (.natural 1) (doubleSafe.final doubleRun) oneBits
    (by simpa only [doubled,two,loaded,loadSlotResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+6≤before.pc+10)).trans pcBits))
  have addRun : linearExecute input [.natOp .add .index .index .flag] one=some added := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,one,doubled,State.set,added]
  have addSafe := PrefixSafe.natOp input one budget .add .index .index .flag (level*2) 1 (level*2+1)
    (oneSafe.final oneRun) (by simp [one,doubled,State.set]) (by simp [one,State.set]) rfl widthBits
    (by simpa only [one,doubled,two,loaded,loadSlotResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+7≤before.pc+10)).trans pcBits))
  have addedFresh : added.register .fresh=.natural base := by
    simp [added,one,doubled,two,loaded,loadSlotResult,State.set,fresh]
  have storeSafe := PrefixSafe.storeSlot input added base 8 budget .index (addSafe.final addRun)
    addedFresh (by decide) eightBits
    (by simpa only [added,one,doubled,two,loaded,loadSlotResult,State.set,Nat.add_assoc] using pcBits)
  have tailSafe := PrefixSafe.append input [.natOp .add .index .index .flag] (storeSlot 8 .index)
    one added budget addRun addSafe storeSafe
  have oneTail := PrefixSafe.append input [.constant .flag (.natural 1)]
    ([.natOp .add .index .index .flag]++storeSlot 8 .index) doubled one budget oneRun oneSafe tailSafe
  have doubleTail := PrefixSafe.append input [.natOp .multiply .index .index .flag]
    ([.constant .flag (.natural 1)]++([.natOp .add .index .index .flag]++storeSlot 8 .index))
    two doubled budget doubleRun doubleSafe oneTail
  have twoTail := PrefixSafe.append input [.constant .flag (.natural 2)]
    ([.natOp .multiply .index .index .flag]++([.constant .flag (.natural 1)]++
      ([.natOp .add .index .index .flag]++storeSlot 8 .index))) loaded two budget twoRun twoSafe doubleTail
  change PrefixSafe input (loadSlot 5 .index++
    ([.constant .flag (.natural 2)]++([.natOp .multiply .index .index .flag]++
      ([.constant .flag (.natural 1)]++([.natOp .add .index .index .flag]++storeSlot 8 .index))))) before budget
  exact PrefixSafe.append input (loadSlot 5 .index)
      ([.constant .flag (.natural 2)]++([.natOp .multiply .index .index .flag]++
        ([.constant .flag (.natural 1)]++([.natOp .add .index .index .flag]++storeSlot 8 .index))))
      before loaded budget loadRun loadSafe twoTail

end PDROC.CalibrationRow.Operand
