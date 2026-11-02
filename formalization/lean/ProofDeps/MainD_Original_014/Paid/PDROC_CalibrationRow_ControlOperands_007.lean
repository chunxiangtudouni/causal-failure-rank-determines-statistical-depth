module

public import Paid.PDROC_CalibrationRow_ControlOperands_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

theorem firstPointer_prefix_safe (input : List Cell) (before : State) (base budget : ℕ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (sixteenBits : (Cell.natural 16).bits≤budget) (pointerBits : (Cell.natural (base+16)).bits≤budget)
    (addressBits : 1+natBits (base+9)≤budget) (pcBits : natBits (before.pc+5)≤budget) :
    PrefixSafe input firstPointerCode before budget := by
  let sixteen := ({before with pc:=before.pc+1}).set .old (.natural 16)
  let computed := ({sixteen with pc:=sixteen.pc+1}).set .old (.natural (base+16))
  have firstRun : linearExecute input [.constant .old (.natural 16)] before=some sixteen := rfl
  have firstSafe := PrefixSafe.constant input before budget .old (.natural 16) safe sixteenBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+1≤before.pc+5)).trans pcBits)
  have addRun : linearExecute input [.natOp .add .old .fresh .old] sixteen=some computed := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,sixteen,State.set,fresh,computed]
  have addSafe := PrefixSafe.natOp input sixteen budget .add .old .fresh .old base 16 (base+16)
    (firstSafe.final firstRun) (by simp [sixteen,State.set,fresh]) (by simp [sixteen,State.set]) rfl pointerBits
    (by simpa only [sixteen,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+2≤before.pc+5)).trans pcBits))
  have computedFresh : computed.register .fresh=.natural base := by simp [computed,sixteen,State.set,fresh]
  have storeSafe := PrefixSafe.storeSlot input computed base 9 budget .old (addSafe.final addRun)
    computedFresh (by decide) addressBits
    (by simpa only [computed,sixteen,State.set,Nat.add_assoc] using pcBits)
  have tail := PrefixSafe.append input [.natOp .add .old .fresh .old] (storeSlot 9 .old)
    sixteen computed budget addRun addSafe storeSafe
  change PrefixSafe input ([.constant .old (.natural 16)]++([.natOp .add .old .fresh .old]++storeSlot 9 .old)) before budget
  exact PrefixSafe.append input [.constant .old (.natural 16)]
    ([.natOp .add .old .fresh .old]++storeSlot 9 .old) before sixteen budget firstRun firstSafe tail

/-- All eleven original second-pointer instructions keep caller B;
M is actually read from live header2. Only each actual new natural is
bounded, with no assumption on unmodified incoming scratch cells. -/
theorem secondPointer_prefix_safe (input : List Cell) (before : State) (base M budget : ℕ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (old : before.register .old=.natural (firstRow base))
    (live : base+2∈before.live) (MValue : before.heap (base+2)=.natural M)
    (twoBits : (Cell.natural 2).bits≤budget) (threeBits : (Cell.natural 3).bits≤budget)
    (doubleBits : (Cell.natural (M*2)).bits≤budget) (widthBits : (Cell.natural (M*2+3)).bits≤budget)
    (pointerBits : (Cell.natural (firstRow base+(M*2+3))).bits≤budget)
    (readBits : 1+natBits (base+2)≤budget) (writeBits : 1+natBits (base+10)≤budget)
    (pcBits : natBits (before.pc+11)≤budget) :
    PrefixSafe input secondPointerCode before budget := by
  let loaded := loadSlotResult before base 2 .index
  let two := ({loaded with pc:=loaded.pc+1}).set .flag (.natural 2)
  let doubled := ({two with pc:=two.pc+1}).set .index (.natural (M*2))
  let three := ({doubled with pc:=doubled.pc+1}).set .flag (.natural 3)
  let width := ({three with pc:=three.pc+1}).set .index (.natural (M*2+3))
  let computed := ({width with pc:=width.pc+1}).set .total (.natural (firstRow base+(M*2+3)))
  have loadRun : linearExecute input (loadSlot 2 .index) before=some loaded :=
    loadSlot_execute input before base 2 .index fresh live
  have loadSafe := PrefixSafe.loadSlot input before base 2 budget .index safe fresh live readBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+3≤before.pc+11)).trans pcBits)
  have twoRun : linearExecute input [.constant .flag (.natural 2)] loaded=some two := rfl
  have twoSafe := PrefixSafe.constant input loaded budget .flag (.natural 2) (loadSafe.final loadRun) twoBits
    (by simpa only [loaded,loadSlotResult,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+11)).trans pcBits))
  have doubleRun : linearExecute input [.natOp .multiply .index .index .flag] two=some doubled := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,two,loaded,loadSlotResult,State.set,MValue,doubled]
  have doubleSafe := PrefixSafe.natOp input two budget .multiply .index .index .flag M 2 (M*2)
    (twoSafe.final twoRun) (by simp [two,loaded,loadSlotResult,State.set,MValue])
    (by simp [two,State.set]) rfl doubleBits
    (by simpa only [two,loaded,loadSlotResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+5≤before.pc+11)).trans pcBits))
  have threeRun : linearExecute input [.constant .flag (.natural 3)] doubled=some three := rfl
  have threeSafe := PrefixSafe.constant input doubled budget .flag (.natural 3) (doubleSafe.final doubleRun) threeBits
    (by simpa only [doubled,two,loaded,loadSlotResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+6≤before.pc+11)).trans pcBits))
  have widthRun : linearExecute input [.natOp .add .index .index .flag] three=some width := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,three,doubled,State.set,width]
  have widthSafe := PrefixSafe.natOp input three budget .add .index .index .flag (M*2) 3 (M*2+3)
    (threeSafe.final threeRun) (by simp [three,doubled,State.set]) (by simp [three,State.set]) rfl widthBits
    (by simpa only [three,doubled,two,loaded,loadSlotResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+7≤before.pc+11)).trans pcBits))
  have computedRun : linearExecute input [.natOp .add .total .old .index] width=some computed := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,width,three,doubled,two,loaded,
      loadSlotResult,State.set,old,computed]
  have computedSafe := PrefixSafe.natOp input width budget .add .total .old .index
    (firstRow base) (M*2+3) (firstRow base+(M*2+3)) (widthSafe.final widthRun)
    (by simp [width,three,doubled,two,loaded,loadSlotResult,State.set,old])
    (by simp [width,State.set]) rfl pointerBits
    (by simpa only [width,three,doubled,two,loaded,loadSlotResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+8≤before.pc+11)).trans pcBits))
  have computedFresh : computed.register .fresh=.natural base := by
    simp [computed,width,three,doubled,two,loaded,loadSlotResult,State.set,fresh]
  have storeSafe := PrefixSafe.storeSlot input computed base 10 budget .total (computedSafe.final computedRun)
    computedFresh (by decide) writeBits
    (by simpa only [computed,width,three,doubled,two,loaded,loadSlotResult,State.set,Nat.add_assoc] using pcBits)
  have computedTail := PrefixSafe.append input [.natOp .add .total .old .index] (storeSlot 10 .total)
    width computed budget computedRun computedSafe storeSafe
  have widthTail := PrefixSafe.append input [.natOp .add .index .index .flag]
    ([.natOp .add .total .old .index]++storeSlot 10 .total) three width budget widthRun widthSafe computedTail
  have threeTail := PrefixSafe.append input [.constant .flag (.natural 3)]
    ([.natOp .add .index .index .flag]++([.natOp .add .total .old .index]++storeSlot 10 .total))
    doubled three budget threeRun threeSafe widthTail
  have doubleTail := PrefixSafe.append input [.natOp .multiply .index .index .flag]
    ([.constant .flag (.natural 3)]++([.natOp .add .index .index .flag]++
      ([.natOp .add .total .old .index]++storeSlot 10 .total))) two doubled budget doubleRun doubleSafe threeTail
  have twoTail := PrefixSafe.append input [.constant .flag (.natural 2)]
    ([.natOp .multiply .index .index .flag]++([.constant .flag (.natural 3)]++
      ([.natOp .add .index .index .flag]++([.natOp .add .total .old .index]++storeSlot 10 .total))))
    loaded two budget twoRun twoSafe doubleTail
  change PrefixSafe input (loadSlot 2 .index++
    ([.constant .flag (.natural 2)]++([.natOp .multiply .index .index .flag]++
      ([.constant .flag (.natural 3)]++([.natOp .add .index .index .flag]++
        ([.natOp .add .total .old .index]++storeSlot 10 .total)))))) before budget
  exact PrefixSafe.append input (loadSlot 2 .index)
    ([.constant .flag (.natural 2)]++([.natOp .multiply .index .index .flag]++
      ([.constant .flag (.natural 3)]++([.natOp .add .index .index .flag]++
        ([.natOp .add .total .old .index]++storeSlot 10 .total))))) before loaded budget loadRun loadSafe twoTail

end PDROC.CalibrationRow.Operand
