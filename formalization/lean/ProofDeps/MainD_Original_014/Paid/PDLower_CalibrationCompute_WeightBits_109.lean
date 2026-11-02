module

public import Paid.PDLower_CalibrationCompute_Weight_033
public import Paid.PDLower_CalibrationCompute_IOPrefix_090
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDROC_CalibrationRow_OperandPrefix_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

/-- The actual endpoint heap read, address arithmetic, two half-minus
operations and real denominator comparison. All new-value inequalities
refer to these concrete operands; arbitrary old scratch keeps caller B. -/
theorem weight_prefix_safe (input : List Cell) (before : State) (base endpoints level budget : ℕ) (error q : ℚ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (endpointLive : base+1∈before.live) (endpointValue : before.heap (base+1)=.natural endpoints)
    (levelLive : base+5∈before.live) (levelValue : before.heap (base+5)=.natural level)
    (qLive : base+11∈before.live) (qValue : before.heap (base+11)=.rational q)
    (errorLive : endpoints+(level*2-1)∈before.live) (errorValue : before.heap (endpoints+(level*2-1))=.rational error)
    (slot1Bits : 1+natBits (base+1)≤budget) (slot5Bits : 1+natBits (base+5)≤budget)
    (slot11Bits : 1+natBits (base+11)≤budget)
    (twiceBits : (Cell.natural (level*2)).bits≤budget) (offsetBits : (Cell.natural (level*2-1)).bits≤budget)
    (addressBits : (Cell.natural (endpoints+(level*2-1))).bits≤budget)
    (zeroNat : (Cell.natural 0).bits≤budget) (oneNat : (Cell.natural 1).bits≤budget) (twoNat : (Cell.natural 2).bits≤budget)
    (halfBits : (Cell.rational (1/2)).bits≤budget) (zeroRat : (Cell.rational 0).bits≤budget)
    (numeratorBits : (Cell.rational (1/2-error)).bits≤budget) (denominatorBits : (Cell.rational (1/2-q)).bits≤budget)
    (pcBits : natBits (before.pc+20)≤budget) : PrefixSafe input (basicBlock .weight).body before budget := by
  let a := loadSlotResult before base 1 .old
  let b := loadSlotResult a base 5 .index
  let c := ({b with pc:=b.pc+1}).set .flag (.natural 2)
  let d := ({c with pc:=c.pc+1}).set .index (.natural (level*2))
  let e := ({d with pc:=d.pc+1}).set .flag (.natural 1)
  let f := ({e with pc:=e.pc+1}).set .index (.natural (level*2-1))
  let g := ({f with pc:=f.pc+1}).set .address (.natural (endpoints+(level*2-1)))
  let h := ({g with pc:=g.pc+1}).set .total (.rational error)
  let i := ({h with pc:=h.pc+1}).set .old (.rational (1/2))
  let j := ({i with pc:=i.pc+1}).set .total (.rational (1/2-error))
  let k := loadSlotResult j base 11 .value
  let l := ({k with pc:=k.pc+1}).set .value (.rational (1/2-q))
  let m := ({l with pc:=l.pc+1}).set .old (.rational 0)
  have pcSmall (offset : ℕ) (bounded : offset≤20) : natBits (before.pc+offset)≤budget :=
    (PDROC.DataBits.natBits_mono (Nat.add_le_add_left bounded before.pc)).trans pcBits
  have aRun : linearExecute input (loadSlot 1 .old) before=some a := loadSlot_execute input before base 1 .old fresh endpointLive
  have aSafe := PrefixSafe.loadSlot input before base 1 budget .old safe fresh endpointLive slot1Bits (pcSmall 3 (by decide))
  have aFresh : a.register .fresh=.natural base := by simp [a,loadSlotResult,fresh]
  have bRun : linearExecute input (loadSlot 5 .index) a=some b := loadSlot_execute input a base 5 .index aFresh levelLive
  have bSafe := PrefixSafe.loadSlot input a base 5 budget .index (aSafe.final aRun) aFresh levelLive slot5Bits
    (by simpa only [a,loadSlotResult,Nat.add_assoc] using pcSmall 6 (by decide))
  have cRun : linearExecute input [.constant .flag (.natural 2)] b=some c := rfl
  have cSafe := PrefixSafe.constant input b budget .flag (.natural 2) (bSafe.final bRun) twoNat
    (by simpa only [b,a,loadSlotResult,Nat.add_assoc] using pcSmall 7 (by decide))
  have dRun : linearExecute input [.natOp .multiply .index .index .flag] c=some d := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,d,c,b,a,loadSlotResult,State.set,levelValue]
  have dSafe := PrefixSafe.natOp input c budget .multiply .index .index .flag level 2 (level*2) (cSafe.final cRun)
    (by simp [c,b,a,loadSlotResult,State.set,levelValue]) (by simp [c,State.set]) rfl twiceBits
    (by simpa only [c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 8 (by decide))
  have eRun : linearExecute input [.constant .flag (.natural 1)] d=some e := rfl
  have eSafe := PrefixSafe.constant input d budget .flag (.natural 1) (dSafe.final dRun) oneNat
    (by simpa only [d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 9 (by decide))
  have fRun : linearExecute input [.natOp .subtract .index .index .flag] e=some f := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,f,e,d,State.set]
  have fSafe := PrefixSafe.natOp input e budget .subtract .index .index .flag (level*2) 1 (level*2-1) (eSafe.final eRun)
    (by simp [e,d,State.set]) (by simp [e,State.set]) rfl offsetBits
    (by simpa only [e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 10 (by decide))
  have gRun : linearExecute input [.natOp .add .address .old .index] f=some g := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,g,f,e,d,c,b,a,loadSlotResult,State.set,endpointValue]
  have gSafe := PrefixSafe.natOp input f budget .add .address .old .index endpoints (level*2-1) (endpoints+(level*2-1))
    (fSafe.final fRun) (by simp [f,e,d,c,b,a,loadSlotResult,State.set,endpointValue])
    (by simp [f,State.set]) rfl addressBits
    (by simpa only [f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 11 (by decide))
  have hRun : linearExecute input [.load .total .address] g=some h := by
    simp [linearExecute,Instruction.execute,Cell.nat?,h,g,f,e,d,c,b,a,loadSlotResult,State.set,errorLive,errorValue]
  have hSafe := PrefixSafe.load input g budget .total .address (endpoints+(level*2-1)) (gSafe.final gRun)
    (by simp [g,State.set]) (by simpa only [g,f,e,d,c,b,a,loadSlotResult,State.set] using errorLive)
    (by simpa only [g,f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 12 (by decide))
  have iRun : linearExecute input [.constant .old (.rational (1/2))] h=some i := rfl
  have iSafe := PrefixSafe.constant input h budget .old (.rational (1/2)) (hSafe.final hRun) halfBits
    (by simpa only [h,g,f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 13 (by decide))
  have jRun : linearExecute input [.ratOp .subtract .total .old .total] i=some j := by
    simp [linearExecute,Instruction.execute,Cell.rat?,RatOp.eval,j,i,h,State.set]
  have jSafe := PrefixSafe.ratOp input i budget .subtract .total .old .total (1/2) error (1/2-error) (iSafe.final iRun)
    (by simp [i,State.set]) (by simp [i,h,State.set]) rfl numeratorBits
    (by simpa only [i,h,g,f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 14 (by decide))
  have jFresh : j.register .fresh=.natural base := by simp [j,i,h,g,f,e,d,c,b,a,loadSlotResult,State.set,fresh]
  have jQLive : base+11∈j.live := by simpa only [j,i,h,g,f,e,d,c,b,a,loadSlotResult,State.set] using qLive
  have kRun : linearExecute input (loadSlot 11 .value) j=some k := loadSlot_execute input j base 11 .value jFresh jQLive
  have kSafe := PrefixSafe.loadSlot input j base 11 budget .value (jSafe.final jRun) jFresh jQLive slot11Bits
    (by simpa only [j,i,h,g,f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 17 (by decide))
  have lRun : linearExecute input [.ratOp .subtract .value .old .value] k=some l := by
    simp [linearExecute,Instruction.execute,Cell.rat?,RatOp.eval,l,k,j,i,h,g,f,e,d,c,b,a,loadSlotResult,State.set,qValue]
  have lSafe := PrefixSafe.ratOp input k budget .subtract .value .old .value (1/2) q (1/2-q) (kSafe.final kRun)
    (by simp [k,j,i,loadSlotResult,State.set])
    (by simp [k,j,i,h,g,f,e,d,c,b,a,loadSlotResult,State.set,qValue]) rfl denominatorBits
    (by simpa only [k,j,i,h,g,f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 18 (by decide))
  have mRun : linearExecute input [.constant .old (.rational 0)] l=some m := rfl
  have mSafe := PrefixSafe.constant input l budget .old (.rational 0) (lSafe.final lRun) zeroRat
    (by simpa only [l,k,j,i,h,g,f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 19 (by decide))
  let rest13 : List Instruction := [.ratCompare .equal .flag .value .old]
  have safe13 : PrefixSafe input rest13 m budget := ratCompare_sameBudget input m .equal .flag .value .old (1/2-q) 0 budget
    (mSafe.final mRun) (by simp [m,l,State.set]) (by simp [m,State.set]) zeroNat oneNat
    (by simpa only [m,l,k,j,i,h,g,f,e,d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 20 (by decide))
  let rest12 : List Instruction := [.constant .old (.rational 0)]++rest13
  have safe12 : PrefixSafe input rest12 l budget := PrefixSafe.append input _ _ l m budget mRun mSafe safe13
  let rest11 : List Instruction := [.ratOp .subtract .value .old .value]++rest12
  have safe11 : PrefixSafe input rest11 k budget := PrefixSafe.append input _ _ k l budget lRun lSafe safe12
  let rest10 : List Instruction := loadSlot 11 .value++rest11
  have safe10 : PrefixSafe input rest10 j budget := PrefixSafe.append input _ _ j k budget kRun kSafe safe11
  let rest9 : List Instruction := [.ratOp .subtract .total .old .total]++rest10
  have safe9 : PrefixSafe input rest9 i budget := PrefixSafe.append input _ _ i j budget jRun jSafe safe10
  let rest8 : List Instruction := [.constant .old (.rational (1/2))]++rest9
  have safe8 : PrefixSafe input rest8 h budget := PrefixSafe.append input _ _ h i budget iRun iSafe safe9
  let rest7 : List Instruction := [.load .total .address]++rest8
  have safe7 : PrefixSafe input rest7 g budget := PrefixSafe.append input _ _ g h budget hRun hSafe safe8
  let rest6 : List Instruction := [.natOp .add .address .old .index]++rest7
  have safe6 : PrefixSafe input rest6 f budget := PrefixSafe.append input _ _ f g budget gRun gSafe safe7
  let rest5 : List Instruction := [.natOp .subtract .index .index .flag]++rest6
  have safe5 : PrefixSafe input rest5 e budget := PrefixSafe.append input _ _ e f budget fRun fSafe safe6
  let rest4 : List Instruction := [.constant .flag (.natural 1)]++rest5
  have safe4 : PrefixSafe input rest4 d budget := PrefixSafe.append input _ _ d e budget eRun eSafe safe5
  let rest3 : List Instruction := [.natOp .multiply .index .index .flag]++rest4
  have safe3 : PrefixSafe input rest3 c budget := PrefixSafe.append input _ _ c d budget dRun dSafe safe4
  let rest2 : List Instruction := [.constant .flag (.natural 2)]++rest3
  have safe2 : PrefixSafe input rest2 b budget := PrefixSafe.append input _ _ b c budget cRun cSafe safe3
  let rest1 : List Instruction := loadSlot 5 .index++rest2
  have safe1 : PrefixSafe input rest1 a budget := PrefixSafe.append input _ _ a b budget bRun bSafe safe2
  let rest0 : List Instruction := loadSlot 1 .old++rest1
  have all : PrefixSafe input rest0 before budget := PrefixSafe.append input _ _ before a budget aRun aSafe safe1
  simpa only [basicBlock,rest0,rest1,rest2,rest3,rest4,rest5,rest6,rest7,rest8,rest9,rest10,rest11,rest12,rest13,
    List.append_assoc,List.cons_append,List.nil_append] using all

theorem weight_bitSegment (origin : ℕ) (input : List Cell) (before : State) (base endpoints level budget : ℕ) (error q : ℚ)
    (position : before.pc=labelAddress origin .weight) (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (endpointLive : base+1∈before.live) (endpointValue : before.heap (base+1)=.natural endpoints)
    (levelLive : base+5∈before.live) (levelValue : before.heap (base+5)=.natural level)
    (qLive : base+11∈before.live) (qValue : before.heap (base+11)=.rational q)
    (errorLive : endpoints+(level*2-1)∈before.live) (errorValue : before.heap (endpoints+(level*2-1))=.rational error)
    (slot1Bits : 1+natBits (base+1)≤budget) (slot5Bits : 1+natBits (base+5)≤budget) (slot11Bits : 1+natBits (base+11)≤budget)
    (twiceBits : (Cell.natural (level*2)).bits≤budget) (offsetBits : (Cell.natural (level*2-1)).bits≤budget)
    (addressBits : (Cell.natural (endpoints+(level*2-1))).bits≤budget)
    (zeroNat : (Cell.natural 0).bits≤budget) (oneNat : (Cell.natural 1).bits≤budget) (twoNat : (Cell.natural 2).bits≤budget)
    (halfBits : (Cell.rational (1/2)).bits≤budget) (zeroRat : (Cell.rational 0).bits≤budget)
    (numeratorBits : (Cell.rational (1/2-error)).bits≤budget) (denominatorBits : (Cell.rational (1/2-q)).bits≤budget)
    (pcBits : natBits (before.pc+20)≤budget) (targets : ∀ label,natBits (labelAddress origin label)≤budget) :
    BitSegment origin input before
      {(weightResult before base endpoints level error q) with
        pc:=labelAddress origin (if (1/2-q : ℚ)=0 then .zeroWeight else .divide)} 330 budget := by
  let middle := weightResult before base endpoints level error q
  let after : State := {middle with pc:=labelAddress origin (if (1/2-q : ℚ)=0 then .zeroWeight else .divide)}
  have body := weight_execute input before base endpoints level error q fresh endpointLive endpointValue levelLive levelValue qLive qValue errorLive errorValue
  have prefixes := weight_prefix_safe input before base endpoints level budget error q safe fresh endpointLive endpointValue levelLive levelValue
    qLive qValue errorLive errorValue slot1Bits slot5Bits slot11Bits twiceBits offsetBits addressBits zeroNat oneNat twoNat halfBits zeroRat numeratorBits denominatorBits pcBits
  have control : (controlInstruction origin (basicBlock .weight).control).execute input middle=some after := by
    simp [basicBlock,controlInstruction,Instruction.execute,middle,weightResult,after,Cell.nat?]
    split_ifs <;> rfl
  have last := control_safe origin (basicBlock .weight).control input middle after budget (prefixes.final body) targets control
  exact BitSegment.ofBlock origin .weight input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed) last

end PDLower.CalibrationCompute
