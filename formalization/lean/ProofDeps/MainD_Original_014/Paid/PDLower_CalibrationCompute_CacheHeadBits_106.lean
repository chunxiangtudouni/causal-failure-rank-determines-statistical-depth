module

public import Paid.PDLower_CalibrationCompute_CacheHead_020
public import Paid.PDLower_CalibrationCompute_IOPrefix_090
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDROC_CalibrationRow_ControlOperands_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem enterCache_prefix_safe (P : Parameters) (origin : ℕ) (input : List Cell) (before : State) (base cursor budget : ℕ)
    (bounds : ControlBudget P origin base budget) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base)
    (sizeLive : base+2∈before.live) (sizeValue : before.heap (base+2)=.natural P.certificate.M)
    (cursorLive : base+15∈before.live) (cursorValue : before.heap (base+15)=.natural cursor)
    (cursorBound : cursor+1≤controlNaturalCap P base) (position : before.pc=labelAddress origin .enterCache) :
    PrefixSafe input (basicBlock .enterCache).body before budget := by
  let a := loadSlotResult before base 2 .value
  let b := ({a with pc:=a.pc+1}).set .flag (.natural 1)
  let c := ({b with pc:=b.pc+1}).set .value (.natural (P.certificate.M+1))
  let d := loadSlotResult c base 15 .index
  let e := writeCell d cursor (.natural (P.certificate.M+1))
  let f : State := {e with pc:=e.pc+1,output:=e.output++[e.register .value]}
  let g := ({f with pc:=f.pc+1}).set .index (.natural (cursor+1))
  let h := storeSlotResult g base 15 .index
  have pcSmall (offset : ℕ) (bounded : offset≤32) : natBits (before.pc+offset)≤budget :=
    ControlBudget.pc_prefix P origin base budget bounds before .enterCache offset position bounded
  have oneBits := ControlBudget.literal P origin base budget 1 bounds (by decide)
  have sizeBits : (Cell.natural (P.certificate.M+1)).bits≤budget :=
    ControlBudget.nat P origin base budget _ bounds (by
      have lower := (controlNaturalCap_lower P base).2.1
      unfold rowWidth at lower
      omega)
  have nextBits := ControlBudget.nat P origin base budget (cursor+1) bounds cursorBound
  have aRun : linearExecute input (loadSlot 2 .value) before=some a := loadSlot_execute input before base 2 .value fresh sizeLive
  have aSafe := PrefixSafe.loadSlot input before base 2 budget .value safe fresh sizeLive
    (ControlBudget.slot P origin base budget 2 bounds (by decide)) (pcSmall 3 (by decide))
  have bRun : linearExecute input [.constant .flag (.natural 1)] a=some b := rfl
  have bSafe := PrefixSafe.constant input a budget .flag (.natural 1) (aSafe.final aRun) oneBits
    (by simpa only [a,loadSlotResult,Nat.add_assoc] using pcSmall 4 (by decide))
  have cRun : linearExecute input [.natOp .add .value .value .flag] b=some c := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,c,b,a,loadSlotResult,State.set,sizeValue]
  have cSafe := PrefixSafe.natOp input b budget .add .value .value .flag P.certificate.M 1 (P.certificate.M+1)
    (bSafe.final bRun) (by simp [b,a,loadSlotResult,State.set,sizeValue]) (by simp [b,State.set]) rfl sizeBits
    (by simpa only [b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 5 (by decide))
  have cFresh : c.register .fresh=.natural base := by simp [c,b,a,loadSlotResult,State.set,fresh]
  have cCursorLive : base+15∈c.live := by simpa only [c,b,a,loadSlotResult,State.set] using cursorLive
  have dRun : linearExecute input (loadSlot 15 .index) c=some d := loadSlot_execute input c base 15 .index cFresh cCursorLive
  have dSafe := PrefixSafe.loadSlot input c base 15 budget .index (cSafe.final cRun) cFresh cCursorLive
    (ControlBudget.slot P origin base budget 15 bounds (by decide))
    (by simpa only [c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 8 (by decide))
  have eRun : linearExecute input [.store .index .value] d=some e := by
    simp [linearExecute,Instruction.execute,Cell.nat?,e,writeCell,d,c,b,a,loadSlotResult,State.set,cursorValue]
  have eSafe := PrefixSafe.store input d budget .index .value cursor (dSafe.final dRun)
    (by simp [d,c,b,a,loadSlotResult,State.set,cursorValue])
    (by simpa only [d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 9 (by decide))
  have fRun : linearExecute input [.output .value] e=some f := rfl
  have fSafe := output_sameBudget input e .value budget (eSafe.final eRun)
    (by simpa only [e,d,c,b,a,writeCell,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 10 (by decide))
  have gRun : linearExecute input [.natOp .add .index .index .flag] f=some g := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,g,f,e,d,c,b,a,writeCell,loadSlotResult,State.set,cursorValue]
  have gSafe := PrefixSafe.natOp input f budget .add .index .index .flag cursor 1 (cursor+1) (fSafe.final fRun)
    (by simp [f,e,d,c,b,a,writeCell,loadSlotResult,State.set,cursorValue])
    (by simp [f,e,d,c,b,writeCell,loadSlotResult,State.set]) rfl nextBits
    (by simpa only [f,e,d,c,b,a,writeCell,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 11 (by decide))
  have gFresh : g.register .fresh=.natural base := by simp [g,f,e,d,c,b,a,writeCell,loadSlotResult,State.set,fresh]
  have hRun : linearExecute input (storeSlot 15 .index) g=some h := storeSlot_execute input g base 15 .index gFresh (by decide)
  have hSafe := PrefixSafe.storeSlot input g base 15 budget .index (gSafe.final gRun) gFresh (by decide)
    (ControlBudget.slot P origin base budget 15 bounds (by decide))
    (by simpa only [g,f,e,d,c,b,a,writeCell,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 14 (by decide))
  have hFresh : h.register .fresh=.natural base := by simp [h,storeSlotResult,gFresh]
  have lastSafe := constantSlot_sameBudget input h base 5 budget (.natural 1) (hSafe.final hRun) hFresh oneBits
    (ControlBudget.slot P origin base budget 5 bounds (by decide))
    (by simpa only [h,g,f,e,d,c,b,a,storeSlotResult,writeCell,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 18 (by decide))
  have tailH := PrefixSafe.append input (storeSlot 15 .index) (constantSlot 5 (.natural 1)) g h budget hRun hSafe lastSafe
  have tailG := PrefixSafe.append input [.natOp .add .index .index .flag]
    (storeSlot 15 .index++constantSlot 5 (.natural 1)) f g budget gRun gSafe tailH
  have tailF := PrefixSafe.append input [.output .value] ([.natOp .add .index .index .flag]++
    (storeSlot 15 .index++constantSlot 5 (.natural 1))) e f budget fRun fSafe tailG
  have tailE := PrefixSafe.append input [.store .index .value] ([.output .value]++
    ([.natOp .add .index .index .flag]++(storeSlot 15 .index++constantSlot 5 (.natural 1)))) d e budget eRun eSafe tailF
  have tailD := PrefixSafe.append input (loadSlot 15 .index) ([.store .index .value]++([.output .value]++
    ([.natOp .add .index .index .flag]++(storeSlot 15 .index++constantSlot 5 (.natural 1))))) c d budget dRun dSafe tailE
  have tailC := PrefixSafe.append input [.natOp .add .value .value .flag] (loadSlot 15 .index++
    ([.store .index .value]++([.output .value]++([.natOp .add .index .index .flag]++
      (storeSlot 15 .index++constantSlot 5 (.natural 1)))))) b c budget cRun cSafe tailD
  have tailB := PrefixSafe.append input [.constant .flag (.natural 1)] ([.natOp .add .value .value .flag]++
    (loadSlot 15 .index++([.store .index .value]++([.output .value]++([.natOp .add .index .index .flag]++
      (storeSlot 15 .index++constantSlot 5 (.natural 1))))))) a b budget bRun bSafe tailC
  have all := PrefixSafe.append input (loadSlot 2 .value) ([.constant .flag (.natural 1)]++
    ([.natOp .add .value .value .flag]++(loadSlot 15 .index++([.store .index .value]++([.output .value]++
      ([.natOp .add .index .index .flag]++(storeSlot 15 .index++constantSlot 5 (.natural 1)))))))) before a budget aRun aSafe tailB
  simpa only [basicBlock,List.append_assoc,List.cons_append,List.nil_append] using all

theorem enterCache_bitSegment (P : Parameters) (origin : ℕ) (input : List Cell) (before : State) (base cursor budget : ℕ)
    (bounds : ControlBudget P origin base budget) (safe : SafeBits before budget)
    (fresh : before.register .fresh=.natural base)
    (sizeLive : base+2∈before.live) (sizeValue : before.heap (base+2)=.natural P.certificate.M)
    (cursorLive : base+15∈before.live) (cursorValue : before.heap (base+15)=.natural cursor)
    (cursorBound : cursor+1≤controlNaturalCap P base) (position : before.pc=labelAddress origin .enterCache) :
    BitSegment origin input before {(enterCacheResult before base P.certificate.M cursor) with pc:=labelAddress origin .enterBias} 300 budget := by
  let middle := enterCacheResult before base P.certificate.M cursor
  let after : State := {middle with pc:=labelAddress origin .enterBias}
  have body : linearExecute input (basicBlock .enterCache).body before=some middle :=
    enterCache_execute input before base _ cursor fresh sizeLive sizeValue cursorLive cursorValue
  have prefixes := enterCache_prefix_safe P origin input before base cursor budget bounds safe fresh sizeLive sizeValue cursorLive cursorValue cursorBound position
  have control : (controlInstruction origin (basicBlock .enterCache).control).execute input middle=some after := rfl
  exact BitSegment.ofBlock origin .enterCache input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed)
    ((prefixes.final body).withPC _ (ControlBudget.pc_target P origin base budget bounds .enterBias))

end PDLower.CalibrationCompute
