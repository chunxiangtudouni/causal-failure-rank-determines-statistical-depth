module

public import Paid.PDLower_CalibrationCompute_SumCell_029
public import Paid.PDROC_CalibrationRow_OperandPrefix_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

/-- Every actual lead prefix of one scalar sum iteration. The caller
supplies the INTRINSIC bit bound on the actual shared-denominator sum,
not a generic doubling of the previous accumulator bound. -/
theorem sumCellLead_prefix_safe (input : List Cell) (before : State)
    (base read cursor budget : ℕ) (q value : ℚ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (index : before.register .index=.natural cursor)
    (readLive : base+9∈before.live) (readValue : before.heap (base+9)=.natural read)
    (sumLive : base+11∈before.live) (sumValue : before.heap (base+11)=.rational q)
    (cellLive : read+cursor∈before.live) (cellValue : before.heap (read+cursor)=.rational value)
    (slot9Bits : 1+natBits (base+9)≤budget) (slot11Bits : 1+natBits (base+11)≤budget)
    (cellAddressBits : (Cell.natural (read+cursor)).bits≤budget)
    (addedBits : (Cell.rational (q+value)).bits≤budget)
    (pcBits : natBits (before.pc+9)≤budget) :
    PrefixSafe input sumCellLeadCode before budget := by
  let a := loadSlotResult before base 9 .old
  let b := ({a with pc:=a.pc+1}).set .address (.natural (read+cursor))
  let c := ({b with pc:=b.pc+1}).set .value (.rational value)
  let d := loadSlotResult c base 11 .old
  have pcSmall (offset : ℕ) (bounded : offset≤9) : natBits (before.pc+offset)≤budget :=
    (PDROC.DataBits.natBits_mono (Nat.add_le_add_left bounded before.pc)).trans pcBits
  have aRun : linearExecute input (loadSlot 9 .old) before=some a :=
    loadSlot_execute input before base 9 .old fresh readLive
  have aSafe := PrefixSafe.loadSlot input before base 9 budget .old safe fresh readLive slot9Bits (pcSmall 3 (by decide))
  have bRun : linearExecute input [.natOp .add .address .old .index] a=some b := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,b,a,loadSlotResult,State.set,readValue,index]
  have bSafe := PrefixSafe.natOp input a budget .add .address .old .index read cursor (read+cursor)
    (aSafe.final aRun) (by simp [a,loadSlotResult,readValue]) (by simp [a,loadSlotResult,index])
    rfl cellAddressBits (by simpa only [a,loadSlotResult,Nat.add_assoc] using pcSmall 4 (by decide))
  have cRun : linearExecute input [.load .value .address] b=some c := by
    simp [linearExecute,Instruction.execute,Cell.nat?,c,b,a,loadSlotResult,State.set,cellLive,cellValue]
  have cSafe := PrefixSafe.load input b budget .value .address (read+cursor) (bSafe.final bRun)
    (by simp [b,State.set]) (by simpa only [b,a,State.set,loadSlotResult] using cellLive)
    (by simpa only [b,a,State.set,loadSlotResult,Nat.add_assoc] using pcSmall 5 (by decide))
  have cFresh : c.register .fresh=.natural base := by simp [c,b,a,State.set,loadSlotResult,fresh]
  have cSumLive : base+11∈c.live := by simpa only [c,b,a,State.set,loadSlotResult] using sumLive
  have dRun : linearExecute input (loadSlot 11 .old) c=some d :=
    loadSlot_execute input c base 11 .old cFresh cSumLive
  have dSafe := PrefixSafe.loadSlot input c base 11 budget .old (cSafe.final cRun) cFresh cSumLive slot11Bits
    (by simpa only [c,b,a,State.set,loadSlotResult,Nat.add_assoc] using pcSmall 8 (by decide))
  have lastSafe := PrefixSafe.ratOp input d budget .add .value .old .value q value (q+value)
    (dSafe.final dRun) (by simp [d,c,b,a,State.set,loadSlotResult,sumValue])
    (by simp [d,c,b,a,State.set,loadSlotResult]) rfl addedBits
    (by simpa only [d,c,b,a,State.set,loadSlotResult,Nat.add_assoc] using pcSmall 9 (by decide))
  have tailSafe := PrefixSafe.append input (loadSlot 11 .old) [.ratOp .add .value .old .value]
    c d budget dRun dSafe lastSafe
  have loadTail := PrefixSafe.append input [.load .value .address]
    (loadSlot 11 .old++[.ratOp .add .value .old .value]) b c budget cRun cSafe tailSafe
  have addTail := PrefixSafe.append input [.natOp .add .address .old .index]
    ([.load .value .address]++(loadSlot 11 .old++[.ratOp .add .value .old .value]))
    a b budget bRun bSafe loadTail
  have all := PrefixSafe.append input (loadSlot 9 .old)
    ([.natOp .add .address .old .index]++([.load .value .address]++
      (loadSlot 11 .old++[.ratOp .add .value .old .value]))) before a budget aRun aSafe addTail
  simpa only [sumCellLeadCode,List.append_assoc,List.cons_append,List.nil_append] using all

end PDLower.CalibrationCompute
