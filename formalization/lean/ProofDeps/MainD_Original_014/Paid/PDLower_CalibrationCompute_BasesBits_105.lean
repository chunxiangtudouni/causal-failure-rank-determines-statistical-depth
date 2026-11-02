module

public import Paid.PDLower_CalibrationCompute_Bases_019
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDROC_CalibrationRow_ControlOperands_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem enterBases_prefix_safe (P : Parameters) (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ)
    (bounds : ControlBudget P origin base budget) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base) (total : before.register .total=.natural P.certificate.M)
    (position : before.pc=labelAddress origin .enterBases) :
    PrefixSafe input (basicBlock .enterBases).body before budget := by
  let a := ({before with pc:=before.pc+1}).set .flag (.natural 2)
  let b := ({a with pc:=a.pc+1}).set .index (.natural (P.certificate.M*2))
  let c := ({b with pc:=b.pc+1}).set .flag (.natural 3)
  let d := ({c with pc:=c.pc+1}).set .index (.natural (rowWidth P.certificate.M))
  let e := ({d with pc:=d.pc+1}).set .old (.natural 16)
  let f := ({e with pc:=e.pc+1}).set .old (.natural (firstRow base))
  let g := storeSlotResult f base 9 .old
  let h := ({g with pc:=g.pc+1}).set .total (.natural (secondRow base P.certificate.M))
  let i := storeSlotResult h base 10 .total
  let j := ({i with pc:=i.pc+1}).set .total (.natural (resultBase base P.certificate.M))
  have pcSmall (offset : ℕ) (bounded : offset≤32) : natBits (before.pc+offset)≤budget :=
    ControlBudget.pc_prefix P origin base budget bounds before .enterBases offset position bounded
  have twiceBits : (Cell.natural (P.certificate.M*2)).bits≤budget :=
    ControlBudget.nat P origin base budget _ bounds (by unfold controlNaturalCap firstRow rowWidth;omega)
  have widthBits : (Cell.natural (rowWidth P.certificate.M)).bits≤budget :=
    ControlBudget.nat P origin base budget _ bounds (controlNaturalCap_lower P base).2.1
  have firstBits : (Cell.natural (firstRow base)).bits≤budget :=
    ControlBudget.nat P origin base budget _ bounds (by unfold controlNaturalCap;omega)
  have secondBits : (Cell.natural (secondRow base P.certificate.M)).bits≤budget :=
    ControlBudget.nat P origin base budget _ bounds (by unfold controlNaturalCap firstRow secondRow;omega)
  have resultBits : (Cell.natural (resultBase base P.certificate.M)).bits≤budget :=
    ControlBudget.nat P origin base budget _ bounds (by unfold controlNaturalCap firstRow resultBase;omega)
  have aRun : linearExecute input [.constant .flag (.natural 2)] before=some a := rfl
  have aSafe := PrefixSafe.constant input before budget .flag (.natural 2) safe
    (ControlBudget.literal P origin base budget 2 bounds (by decide)) (pcSmall 1 (by decide))
  have bRun : linearExecute input [.natOp .multiply .index .total .flag] a=some b := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,b,a,State.set,total]
  have bSafe := PrefixSafe.natOp input a budget .multiply .index .total .flag P.certificate.M 2 (P.certificate.M*2)
    (aSafe.final aRun) (by simp [a,State.set,total]) (by simp [a,State.set]) rfl twiceBits
    (by simpa only [a,State.set,Nat.add_assoc] using pcSmall 2 (by decide))
  have cRun : linearExecute input [.constant .flag (.natural 3)] b=some c := rfl
  have cSafe := PrefixSafe.constant input b budget .flag (.natural 3) (bSafe.final bRun)
    (ControlBudget.literal P origin base budget 3 bounds (by decide))
    (by simpa only [b,a,State.set,Nat.add_assoc] using pcSmall 3 (by decide))
  have dRun : linearExecute input [.natOp .add .index .index .flag] c=some d := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,d,c,b,State.set,rowWidth,Nat.mul_comm]
  have dSafe := PrefixSafe.natOp input c budget .add .index .index .flag (P.certificate.M*2) 3 (rowWidth P.certificate.M)
    (cSafe.final cRun) (by simp [c,b,State.set]) (by simp [c,State.set])
    (by simp [NatOp.eval,rowWidth,Nat.mul_comm]) widthBits
    (by simpa only [c,b,a,State.set,Nat.add_assoc] using pcSmall 4 (by decide))
  have eRun : linearExecute input [.constant .old (.natural 16)] d=some e := rfl
  have eSafe := PrefixSafe.constant input d budget .old (.natural 16) (dSafe.final dRun)
    (ControlBudget.literal P origin base budget 16 bounds (by decide))
    (by simpa only [d,c,b,a,State.set,Nat.add_assoc] using pcSmall 5 (by decide))
  have fRun : linearExecute input [.natOp .add .old .fresh .old] e=some f := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,f,e,d,c,b,a,State.set,firstRow,fresh]
  have fSafe := PrefixSafe.natOp input e budget .add .old .fresh .old base 16 (firstRow base) (eSafe.final eRun)
    (by simp [e,d,c,b,a,State.set,fresh]) (by simp [e,State.set]) rfl firstBits
    (by simpa only [e,d,c,b,a,State.set,Nat.add_assoc] using pcSmall 6 (by decide))
  have fFresh : f.register .fresh=.natural base := by simp [f,e,d,c,b,a,State.set,fresh]
  have gRun : linearExecute input (storeSlot 9 .old) f=some g := storeSlot_execute input f base 9 .old fFresh (by decide)
  have gSafe := PrefixSafe.storeSlot input f base 9 budget .old (fSafe.final fRun) fFresh (by decide)
    (ControlBudget.slot P origin base budget 9 bounds (by decide))
    (by simpa only [f,e,d,c,b,a,State.set,Nat.add_assoc] using pcSmall 9 (by decide))
  have hRun : linearExecute input [.natOp .add .total .old .index] g=some h := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,h,g,f,e,d,storeSlotResult,State.set,firstRow,secondRow]
  have hSafe := PrefixSafe.natOp input g budget .add .total .old .index (firstRow base) (rowWidth P.certificate.M)
    (secondRow base P.certificate.M) (gSafe.final gRun) (by simp [g,f,storeSlotResult,State.set])
    (by simp [g,f,e,d,storeSlotResult,State.set]) rfl secondBits
    (by simpa only [g,f,e,d,c,b,a,storeSlotResult,State.set,Nat.add_assoc] using pcSmall 10 (by decide))
  have hFresh : h.register .fresh=.natural base := by simp [h,g,storeSlotResult,State.set,fFresh]
  have iRun : linearExecute input (storeSlot 10 .total) h=some i := storeSlot_execute input h base 10 .total hFresh (by decide)
  have iSafe := PrefixSafe.storeSlot input h base 10 budget .total (hSafe.final hRun) hFresh (by decide)
    (ControlBudget.slot P origin base budget 10 bounds (by decide))
    (by simpa only [h,g,f,e,d,c,b,a,storeSlotResult,State.set,Nat.add_assoc] using pcSmall 13 (by decide))
  have jRun : linearExecute input [.natOp .add .total .total .index] i=some j := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,j,i,h,g,f,e,d,storeSlotResult,State.set,
      firstRow,secondRow,resultBase,two_mul,Nat.add_assoc]
  have jSafe := PrefixSafe.natOp input i budget .add .total .total .index (secondRow base P.certificate.M) (rowWidth P.certificate.M)
    (resultBase base P.certificate.M) (iSafe.final iRun) (by simp [i,h,storeSlotResult,State.set])
    (by simp [i,h,g,f,e,d,storeSlotResult,State.set])
    (by simp [NatOp.eval,secondRow,resultBase,two_mul,Nat.add_assoc]) resultBits
    (by simpa only [i,h,g,f,e,d,c,b,a,storeSlotResult,State.set,Nat.add_assoc] using pcSmall 14 (by decide))
  have jFresh : j.register .fresh=.natural base := by simp [j,i,storeSlotResult,State.set,hFresh]
  have lastSafe := PrefixSafe.storeSlot input j base 15 budget .total (jSafe.final jRun) jFresh (by decide)
    (ControlBudget.slot P origin base budget 15 bounds (by decide))
    (by simpa only [j,i,h,g,f,e,d,c,b,a,storeSlotResult,State.set,Nat.add_assoc] using pcSmall 17 (by decide))
  have tailJ := PrefixSafe.append input [.natOp .add .total .total .index] (storeSlot 15 .total) i j budget jRun jSafe lastSafe
  have tailI := PrefixSafe.append input (storeSlot 10 .total) ([.natOp .add .total .total .index]++storeSlot 15 .total)
    h i budget iRun iSafe tailJ
  have tailH := PrefixSafe.append input [.natOp .add .total .old .index]
    (storeSlot 10 .total++([.natOp .add .total .total .index]++storeSlot 15 .total)) g h budget hRun hSafe tailI
  have tailG := PrefixSafe.append input (storeSlot 9 .old) ([.natOp .add .total .old .index]++
    (storeSlot 10 .total++([.natOp .add .total .total .index]++storeSlot 15 .total))) f g budget gRun gSafe tailH
  have tailF := PrefixSafe.append input [.natOp .add .old .fresh .old] (storeSlot 9 .old++
    ([.natOp .add .total .old .index]++(storeSlot 10 .total++([.natOp .add .total .total .index]++storeSlot 15 .total)))) e f budget fRun fSafe tailG
  have tailE := PrefixSafe.append input [.constant .old (.natural 16)] ([.natOp .add .old .fresh .old]++
    (storeSlot 9 .old++([.natOp .add .total .old .index]++(storeSlot 10 .total++([.natOp .add .total .total .index]++storeSlot 15 .total))))) d e budget eRun eSafe tailF
  have tailD := PrefixSafe.append input [.natOp .add .index .index .flag] ([.constant .old (.natural 16)]++
    ([.natOp .add .old .fresh .old]++(storeSlot 9 .old++([.natOp .add .total .old .index]++
      (storeSlot 10 .total++([.natOp .add .total .total .index]++storeSlot 15 .total)))))) c d budget dRun dSafe tailE
  have tailC := PrefixSafe.append input [.constant .flag (.natural 3)] ([.natOp .add .index .index .flag]++
    ([.constant .old (.natural 16)]++([.natOp .add .old .fresh .old]++(storeSlot 9 .old++
      ([.natOp .add .total .old .index]++(storeSlot 10 .total++([.natOp .add .total .total .index]++storeSlot 15 .total))))))) b c budget cRun cSafe tailD
  have tailB := PrefixSafe.append input [.natOp .multiply .index .total .flag] ([.constant .flag (.natural 3)]++
    ([.natOp .add .index .index .flag]++([.constant .old (.natural 16)]++([.natOp .add .old .fresh .old]++
      (storeSlot 9 .old++([.natOp .add .total .old .index]++(storeSlot 10 .total++([.natOp .add .total .total .index]++storeSlot 15 .total)))))))) a b budget bRun bSafe tailC
  have all := PrefixSafe.append input [.constant .flag (.natural 2)] ([.natOp .multiply .index .total .flag]++
    ([.constant .flag (.natural 3)]++([.natOp .add .index .index .flag]++([.constant .old (.natural 16)]++
      ([.natOp .add .old .fresh .old]++(storeSlot 9 .old++([.natOp .add .total .old .index]++
        (storeSlot 10 .total++([.natOp .add .total .total .index]++storeSlot 15 .total))))))))) before a budget aRun aSafe tailB
  simpa only [basicBlock,List.append_assoc,List.cons_append,List.nil_append] using all

theorem enterBases_bitSegment (P : Parameters) (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ)
    (bounds : ControlBudget P origin base budget) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base) (total : before.register .total=.natural P.certificate.M)
    (position : before.pc=labelAddress origin .enterBases) :
    BitSegment origin input before {(enterBasesResult before base P.certificate.M) with pc:=labelAddress origin .enterCache} 285 budget := by
  let middle := enterBasesResult before base P.certificate.M
  let after : State := {middle with pc:=labelAddress origin .enterCache}
  have body : linearExecute input (basicBlock .enterBases).body before=some middle := enterBases_execute input before base _ fresh total
  have prefixes := enterBases_prefix_safe P origin input before base budget bounds safe fresh total position
  have control : (controlInstruction origin (basicBlock .enterBases).control).execute input middle=some after := rfl
  exact BitSegment.ofBlock origin .enterBases input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed)
    ((prefixes.final body).withPC _ (ControlBudget.pc_target P origin base budget bounds .enterCache))

end PDLower.CalibrationCompute
