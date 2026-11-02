module

public import Paid.PDLower_CalibrationCompute_Finish_036
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDLower_CalibrationCompute_RowBitBudget_102

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem finish_prefix_safe (P : Parameters) (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ) (header : Header)
    (bounds : ControlBudget P origin base budget) (represented : header.At before base)
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before budget)
    (M : header.M=P.certificate.M) (position : before.pc=labelAddress origin .finish) :
    PrefixSafe input (basicBlock .finish).body before budget := by
  have ret := represented.lookup (offset:=0) (value:=.natural header.returnPC) rfl
  have size := represented.lookup (offset:=2) (value:=.natural header.M) rfl
  let a := loadSlotResult before base 0 .old
  let b := loadSlotResult a base 2 .index
  let c := ({b with pc:=b.pc+1}).set .flag (.natural 2)
  let d := ({c with pc:=c.pc+1}).set .index (.natural (P.certificate.M*2))
  let e := ({d with pc:=d.pc+1}).set .flag (.natural 3)
  let f := ({e with pc:=e.pc+1}).set .index (.natural (rowWidth P.certificate.M))
  let g := ({f with pc:=f.pc+1}).set .flag (.natural 2)
  let h := ({g with pc:=g.pc+1}).set .value (.natural (rowWidth P.certificate.M*2))
  let i := ({h with pc:=h.pc+1}).set .flag (.natural 16)
  let j := ({i with pc:=i.pc+1}).set .value (.natural (rowWidth P.certificate.M*2+16))
  have pcSmall (offset : ℕ) (bounded : offset≤32) : natBits (before.pc+offset)≤budget :=
    ControlBudget.pc_prefix P origin base budget bounds before .finish offset position bounded
  have twoBits := ControlBudget.literal P origin base budget 2 bounds (by decide)
  have threeBits := ControlBudget.literal P origin base budget 3 bounds (by decide)
  have sixteenBits := ControlBudget.literal P origin base budget 16 bounds (by decide)
  have twiceBits : (Cell.natural (P.certificate.M*2)).bits≤budget :=
    ControlBudget.nat P origin base budget _ bounds (by unfold controlNaturalCap firstRow rowWidth;omega)
  have widthBits : (Cell.natural (rowWidth P.certificate.M)).bits≤budget :=
    ControlBudget.nat P origin base budget _ bounds (controlNaturalCap_lower P base).2.1
  have pairBits : (Cell.natural (rowWidth P.certificate.M*2)).bits≤budget :=
    ControlBudget.nat P origin base budget _ bounds (by unfold controlNaturalCap firstRow;omega)
  have shiftedBits : (Cell.natural (rowWidth P.certificate.M*2+16)).bits≤budget :=
    ControlBudget.nat P origin base budget _ bounds (by unfold controlNaturalCap firstRow;omega)
  have resultBits : (Cell.natural (resultBase base P.certificate.M)).bits≤budget :=
    ControlBudget.nat P origin base budget _ bounds (by unfold controlNaturalCap firstRow resultBase;omega)
  have aRun : linearExecute input (loadSlot 0 .old) before=some a := loadSlot_execute input before base 0 .old fresh ret.2
  have aSafe := PrefixSafe.loadSlot input before base 0 budget .old safe fresh ret.2
    (ControlBudget.slot P origin base budget 0 bounds (by decide)) (pcSmall 3 (by decide))
  have aFresh : a.register .fresh=.natural base := by simp [a,loadSlotResult,fresh]
  have bRun : linearExecute input (loadSlot 2 .index) a=some b := loadSlot_execute input a base 2 .index aFresh size.2
  have bSafe := PrefixSafe.loadSlot input a base 2 budget .index (aSafe.final aRun) aFresh size.2
    (ControlBudget.slot P origin base budget 2 bounds (by decide))
    (by simpa only [a,loadSlotResult,Nat.add_assoc] using pcSmall 6 (by decide))
  have cRun : linearExecute input [.constant .flag (.natural 2)] b=some c := rfl
  have cSafe := PrefixSafe.constant input b budget .flag (.natural 2) (bSafe.final bRun) twoBits
    (by simpa only [b,a,loadSlotResult,Nat.add_assoc] using pcSmall 7 (by decide))
  have dRun : linearExecute input [.natOp .multiply .index .index .flag] c=some d := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,d,c,b,a,loadSlotResult,State.set,size.1,M]
  have dSafe := PrefixSafe.natOp input c budget .multiply .index .index .flag P.certificate.M 2 (P.certificate.M*2)
    (cSafe.final cRun) (by simp [c,b,a,loadSlotResult,State.set,size.1,M]) (by simp [c,State.set]) rfl twiceBits
    (by simpa only [c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 8 (by decide))
  have eRun : linearExecute input [.constant .flag (.natural 3)] d=some e := rfl
  have eSafe := PrefixSafe.constant input d budget .flag (.natural 3) (dSafe.final dRun) threeBits
    (by simpa only [d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 9 (by decide))
  have fRun : linearExecute input [.natOp .add .index .index .flag] e=some f := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,f,e,d,State.set,rowWidth,Nat.mul_comm]
  have fSafe := PrefixSafe.natOp input e budget .add .index .index .flag (P.certificate.M*2) 3 (rowWidth P.certificate.M)
    (eSafe.final eRun) (by simp [e,d,State.set]) (by simp [e,State.set])
    (by simp [NatOp.eval,rowWidth,Nat.mul_comm]) widthBits
    (by simpa only [e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 10 (by decide))
  have gRun : linearExecute input [.constant .flag (.natural 2)] f=some g := rfl
  have gSafe := PrefixSafe.constant input f budget .flag (.natural 2) (fSafe.final fRun) twoBits
    (by simpa only [f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 11 (by decide))
  have hRun : linearExecute input [.natOp .multiply .value .index .flag] g=some h := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,h,g,f,State.set]
  have hSafe := PrefixSafe.natOp input g budget .multiply .value .index .flag (rowWidth P.certificate.M) 2 (rowWidth P.certificate.M*2)
    (gSafe.final gRun) (by simp [g,f,State.set]) (by simp [g,State.set]) rfl pairBits
    (by simpa only [g,f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 12 (by decide))
  have iRun : linearExecute input [.constant .flag (.natural 16)] h=some i := rfl
  have iSafe := PrefixSafe.constant input h budget .flag (.natural 16) (hSafe.final hRun) sixteenBits
    (by simpa only [h,g,f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 13 (by decide))
  have jRun : linearExecute input [.natOp .add .value .value .flag] i=some j := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,j,i,h,State.set]
  have jSafe := PrefixSafe.natOp input i budget .add .value .value .flag (rowWidth P.certificate.M*2) 16 (rowWidth P.certificate.M*2+16)
    (iSafe.final iRun) (by simp [i,h,State.set]) (by simp [i,State.set]) rfl shiftedBits
    (by simpa only [i,h,g,f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 14 (by decide))
  have lastSafe := PrefixSafe.natOp input j budget .add .address .fresh .value base (rowWidth P.certificate.M*2+16)
    (resultBase base P.certificate.M) (jSafe.final jRun)
    (by simp [j,i,h,g,f,e,d,c,b,a,loadSlotResult,State.set,fresh]) (by simp [j,State.set])
    (by simp [NatOp.eval,resultBase,mul_two,two_mul,Nat.add_comm,Nat.add_assoc]) resultBits
    (by simpa only [j,i,h,g,f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 15 (by decide))
  let rest10 : List Instruction := [.natOp .add .address .fresh .value]
  let rest9 : List Instruction := [.natOp .add .value .value .flag]++rest10
  have safe9 : PrefixSafe input rest9 i budget := PrefixSafe.append input _ _ i j budget jRun jSafe lastSafe
  let rest8 : List Instruction := [.constant .flag (.natural 16)]++rest9
  have safe8 : PrefixSafe input rest8 h budget := PrefixSafe.append input _ _ h i budget iRun iSafe safe9
  let rest7 : List Instruction := [.natOp .multiply .value .index .flag]++rest8
  have safe7 : PrefixSafe input rest7 g budget := PrefixSafe.append input _ _ g h budget hRun hSafe safe8
  let rest6 : List Instruction := [.constant .flag (.natural 2)]++rest7
  have safe6 : PrefixSafe input rest6 f budget := PrefixSafe.append input _ _ f g budget gRun gSafe safe7
  let rest5 : List Instruction := [.natOp .add .index .index .flag]++rest6
  have safe5 : PrefixSafe input rest5 e budget := PrefixSafe.append input _ _ e f budget fRun fSafe safe6
  let rest4 : List Instruction := [.constant .flag (.natural 3)]++rest5
  have safe4 : PrefixSafe input rest4 d budget := PrefixSafe.append input _ _ d e budget eRun eSafe safe5
  let rest3 : List Instruction := [.natOp .multiply .index .index .flag]++rest4
  have safe3 : PrefixSafe input rest3 c budget := PrefixSafe.append input _ _ c d budget dRun dSafe safe4
  let rest2 : List Instruction := [.constant .flag (.natural 2)]++rest3
  have safe2 : PrefixSafe input rest2 b budget := PrefixSafe.append input _ _ b c budget cRun cSafe safe3
  let rest1 : List Instruction := loadSlot 2 .index++rest2
  have safe1 : PrefixSafe input rest1 a budget := PrefixSafe.append input _ _ a b budget bRun bSafe safe2
  let rest0 : List Instruction := loadSlot 0 .old++rest1
  have all : PrefixSafe input rest0 before budget := PrefixSafe.append input _ _ before a budget aRun aSafe safe1
  simpa only [basicBlock,rest0,rest1,rest2,rest3,rest4,rest5,rest6,rest7,rest8,rest9,rest10,
    List.append_assoc,List.cons_append,List.nil_append] using all

theorem finish_bitSegment (P : Parameters) (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ) (header : Header)
    (bounds : ControlBudget P origin base budget) (represented : header.At before base)
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before budget)
    (M : header.M=P.certificate.M) (position : before.pc=labelAddress origin .finish) :
    BitSegment origin input before {(finishResult before base header.M) with pc:=header.returnPC} 255 budget := by
  let middle := finishResult before base header.M
  let after : State := {middle with pc:=header.returnPC}
  have body := finish_execute input before base header represented fresh
  have prefixes := finish_prefix_safe P origin input before base budget header bounds represented fresh safe M position
  have registers := finish_registers before base header represented fresh
  have actualOld : middle.register .old=.natural header.returnPC := registers.1
  have oldBits := (prefixes.final body).register .old
  rw [actualOld] at oldBits
  have returnBits : natBits header.returnPC≤budget := by change 1+natBits header.returnPC≤budget at oldBits;omega
  have control : (controlInstruction origin (basicBlock .finish).control).execute input middle=some after := by
    simp [basicBlock,controlInstruction,Instruction.execute,actualOld,Cell.nat?,after]
  exact BitSegment.ofBlock origin .finish input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed) ((prefixes.final body).withPC _ returnBits)

end PDLower.CalibrationCompute
