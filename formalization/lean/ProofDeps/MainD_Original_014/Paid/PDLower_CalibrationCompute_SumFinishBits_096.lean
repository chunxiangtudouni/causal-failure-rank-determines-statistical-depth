module

public import Paid.PDLower_CalibrationCompute_SumFinish_034
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDROC_CalibrationRow_OperandPrefix_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem sumFinish_prefix_safe (input : List Cell) (before : State) (base budget : ℕ) (header : Header)
    (row : Array ℚ) (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (inside : header.level<row.size) (fresh : before.register .fresh=.natural base) (safe : SafeBits before budget)
    (slot5Bits : 1+natBits (base+5)≤budget) (slot9Bits : 1+natBits (base+9)≤budget)
    (slot11Bits : 1+natBits (base+11)≤budget)
    (cellAddressBits : (Cell.natural (header.readBase+header.level)).bits≤budget)
    (halfBits : (Cell.rational (1/2)).bits≤budget)
    (centerHalfBits : (Cell.rational (row.getD header.level 0*(1/2))).bits≤budget)
    (addedBits : (Cell.rational (header.q+row.getD header.level 0*(1/2))).bits≤budget)
    (pcBits : natBits (before.pc+17)≤budget) :
    PrefixSafe input (basicBlock .sumFinish).body before budget := by
  have level := represented.lookup (offset:=5) (value:=.natural header.level) rfl
  have read := represented.lookup (offset:=9) (value:=.natural header.readBase) rfl
  have sum := represented.lookup (offset:=11) (value:=.rational header.q) rfl
  let a := loadSlotResult before base 5 .index
  let b := loadSlotResult a base 9 .old
  let c := ({b with pc:=b.pc+1}).set .address (.natural (header.readBase+header.level))
  let d := ({c with pc:=c.pc+1}).set .value (.rational (row.getD header.level 0))
  let e := ({d with pc:=d.pc+1}).set .old (.rational (1/2))
  let f := ({e with pc:=e.pc+1}).set .value (.rational (row.getD header.level 0*(1/2)))
  let g := loadSlotResult f base 11 .old
  let h := ({g with pc:=g.pc+1}).set .value (.rational (header.q+row.getD header.level 0*(1/2)))
  have pcSmall (offset : ℕ) (bounded : offset≤17) : natBits (before.pc+offset)≤budget :=
    (PDROC.DataBits.natBits_mono (Nat.add_le_add_left bounded before.pc)).trans pcBits
  have aRun : linearExecute input (loadSlot 5 .index) before=some a :=
    loadSlot_execute input before base 5 .index fresh level.2
  have aSafe := PrefixSafe.loadSlot input before base 5 budget .index safe fresh level.2 slot5Bits (pcSmall 3 (by decide))
  have aFresh : a.register .fresh=.natural base := by simp [a,loadSlotResult,fresh]
  have bRun : linearExecute input (loadSlot 9 .old) a=some b := loadSlot_execute input a base 9 .old aFresh read.2
  have bSafe := PrefixSafe.loadSlot input a base 9 budget .old (aSafe.final aRun) aFresh read.2 slot9Bits
    (by simpa only [a,loadSlotResult,Nat.add_assoc] using pcSmall 6 (by decide))
  have cRun : linearExecute input [.natOp .add .address .old .index] b=some c := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,c,b,a,loadSlotResult,State.set,read.1,level.1]
  have cSafe := PrefixSafe.natOp input b budget .add .address .old .index header.readBase header.level
    (header.readBase+header.level) (bSafe.final bRun) (by simp [b,a,loadSlotResult,read.1])
    (by simp [b,a,loadSlotResult,level.1]) rfl cellAddressBits
    (by simpa only [b,a,loadSlotResult,Nat.add_assoc] using pcSmall 7 (by decide))
  have dRun : linearExecute input [.load .value .address] c=some d := by
    simp [linearExecute,Instruction.execute,Cell.nat?,d,c,b,a,loadSlotResult,State.set,rowAt.live _ inside,rowAt.value _ inside]
  have dSafe := PrefixSafe.load input c budget .value .address (header.readBase+header.level) (cSafe.final cRun)
    (by simp [c,State.set]) (by simpa only [c,b,a,State.set,loadSlotResult] using rowAt.live _ inside)
    (by simpa only [c,b,a,State.set,loadSlotResult,Nat.add_assoc] using pcSmall 8 (by decide))
  have eRun : linearExecute input [.constant .old (.rational (1/2))] d=some e := rfl
  have eSafe := PrefixSafe.constant input d budget .old (.rational (1/2)) (dSafe.final dRun) halfBits
    (by simpa only [d,c,b,a,State.set,loadSlotResult,Nat.add_assoc] using pcSmall 9 (by decide))
  have fRun : linearExecute input [.ratOp .multiply .value .value .old] e=some f := by
    simp [linearExecute,Instruction.execute,Cell.rat?,RatOp.eval,f,e,d,State.set]
  have fSafe := PrefixSafe.ratOp input e budget .multiply .value .value .old (row.getD header.level 0) (1/2)
    (row.getD header.level 0*(1/2)) (eSafe.final eRun) (by simp [e,d,State.set]) (by simp [e,State.set]) rfl centerHalfBits
    (by simpa only [e,d,c,b,a,State.set,loadSlotResult,Nat.add_assoc] using pcSmall 10 (by decide))
  have fFresh : f.register .fresh=.natural base := by simp [f,e,d,c,b,a,State.set,loadSlotResult,fresh]
  have fSumLive : base+11∈f.live := by simpa only [f,e,d,c,b,a,State.set,loadSlotResult] using sum.2
  have gRun : linearExecute input (loadSlot 11 .old) f=some g := loadSlot_execute input f base 11 .old fFresh fSumLive
  have gSafe := PrefixSafe.loadSlot input f base 11 budget .old (fSafe.final fRun) fFresh fSumLive slot11Bits
    (by simpa only [f,e,d,c,b,a,State.set,loadSlotResult,Nat.add_assoc] using pcSmall 13 (by decide))
  have hRun : linearExecute input [.ratOp .add .value .old .value] g=some h := by
    simp [linearExecute,Instruction.execute,Cell.rat?,RatOp.eval,h,g,f,e,d,c,b,a,State.set,loadSlotResult,sum.1]
  have hSafe := PrefixSafe.ratOp input g budget .add .value .old .value header.q (row.getD header.level 0*(1/2))
    (header.q+row.getD header.level 0*(1/2)) (gSafe.final gRun)
    (by simp [g,f,e,d,c,b,a,State.set,loadSlotResult,sum.1]) (by simp [g,f,loadSlotResult,State.set]) rfl addedBits
    (by simpa only [g,f,e,d,c,b,a,State.set,loadSlotResult,Nat.add_assoc] using pcSmall 14 (by decide))
  have hFresh : h.register .fresh=.natural base := by simp [h,g,f,e,d,c,b,a,State.set,loadSlotResult,fresh]
  have storeSafe := PrefixSafe.storeSlot input h base 11 budget .value (hSafe.final hRun) hFresh (by decide) slot11Bits
    (by simpa only [h,g,f,e,d,c,b,a,State.set,loadSlotResult,Nat.add_assoc] using pcSmall 17 (by decide))
  have tailH := PrefixSafe.append input [.ratOp .add .value .old .value] (storeSlot 11 .value) g h budget hRun hSafe storeSafe
  have tailG := PrefixSafe.append input (loadSlot 11 .old) ([.ratOp .add .value .old .value]++storeSlot 11 .value)
    f g budget gRun gSafe tailH
  have tailF := PrefixSafe.append input [.ratOp .multiply .value .value .old]
    (loadSlot 11 .old++([.ratOp .add .value .old .value]++storeSlot 11 .value)) e f budget fRun fSafe tailG
  have tailE := PrefixSafe.append input [.constant .old (.rational (1/2))]
    ([.ratOp .multiply .value .value .old]++(loadSlot 11 .old++([.ratOp .add .value .old .value]++storeSlot 11 .value)))
    d e budget eRun eSafe tailF
  have tailD := PrefixSafe.append input [.load .value .address]
    ([.constant .old (.rational (1/2))]++([.ratOp .multiply .value .value .old]++
      (loadSlot 11 .old++([.ratOp .add .value .old .value]++storeSlot 11 .value)))) c d budget dRun dSafe tailE
  have tailC := PrefixSafe.append input [.natOp .add .address .old .index]
    ([.load .value .address]++([.constant .old (.rational (1/2))]++([.ratOp .multiply .value .value .old]++
      (loadSlot 11 .old++([.ratOp .add .value .old .value]++storeSlot 11 .value))))) b c budget cRun cSafe tailD
  have tailB := PrefixSafe.append input (loadSlot 9 .old)
    ([.natOp .add .address .old .index]++([.load .value .address]++([.constant .old (.rational (1/2))]++
      ([.ratOp .multiply .value .value .old]++(loadSlot 11 .old++([.ratOp .add .value .old .value]++storeSlot 11 .value))))))
    a b budget bRun bSafe tailC
  have all := PrefixSafe.append input (loadSlot 5 .index)
    (loadSlot 9 .old++([.natOp .add .address .old .index]++([.load .value .address]++
      ([.constant .old (.rational (1/2))]++([.ratOp .multiply .value .value .old]++
        (loadSlot 11 .old++([.ratOp .add .value .old .value]++storeSlot 11 .value))))))) before a budget aRun aSafe tailB
  simpa only [basicBlock,List.append_assoc,List.cons_append,List.nil_append] using all

theorem sumFinish_bitSegment (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ) (header : Header)
    (row : Array ℚ) (position : before.pc=labelAddress origin .sumFinish)
    (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (inside : header.level<row.size) (fresh : before.register .fresh=.natural base) (safe : SafeBits before budget)
    (slot5Bits : 1+natBits (base+5)≤budget) (slot9Bits : 1+natBits (base+9)≤budget)
    (slot11Bits : 1+natBits (base+11)≤budget)
    (cellAddressBits : (Cell.natural (header.readBase+header.level)).bits≤budget)
    (halfBits : (Cell.rational (1/2)).bits≤budget)
    (centerHalfBits : (Cell.rational (row.getD header.level 0*(1/2))).bits≤budget)
    (addedBits : (Cell.rational (header.q+row.getD header.level 0*(1/2))).bits≤budget)
    (pcBits : natBits (before.pc+17)≤budget) (targetBits : natBits (labelAddress origin .weight)≤budget) :
    BitSegment origin input before
      {(sumFinishResult before base header.readBase header.level header.q (row.getD header.level 0)) with
        pc:=labelAddress origin .weight} 285 budget := by
  let middle := sumFinishResult before base header.readBase header.level header.q (row.getD header.level 0)
  let after : State := {middle with pc:=labelAddress origin .weight}
  have body : linearExecute input (basicBlock .sumFinish).body before=some middle :=
    sumFinish_execute input before base header row represented rowAt inside fresh
  have prefixes := sumFinish_prefix_safe input before base budget header row represented rowAt inside fresh safe
    slot5Bits slot9Bits slot11Bits cellAddressBits halfBits centerHalfBits addedBits pcBits
  have control : (controlInstruction origin (basicBlock .sumFinish).control).execute input middle=some after := rfl
  exact BitSegment.ofBlock origin .sumFinish input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed) ((prefixes.final body).withPC _ targetBits)

end PDLower.CalibrationCompute
