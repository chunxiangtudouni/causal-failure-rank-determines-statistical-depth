module

public import Paid.PDLower_CalibrationCompute_Emit_035
public import Paid.PDLower_CalibrationCompute_IOPrefix_090
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDLower_CalibrationCompute_RowBitBudget_102
public import Paid.PDROC_CalibrationRow_OperandPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

/-- Both actual stores AND both actual stream appends preserve caller B.
Existing output/live cells retain carry; no result-cell liveness is needed. -/
theorem emitLead_prefix_safe (input : List Cell) (before : State) (base cursor budget : ℕ) (q weight : ℚ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base) (value : before.register .value=.rational weight)
    (cursorLive : base+15∈before.live) (cursorValue : before.heap (base+15)=.natural cursor)
    (qLive : base+11∈before.live) (qValue : before.heap (base+11)=.rational q)
    (slot15Bits : 1+natBits (base+15)≤budget) (slot11Bits : 1+natBits (base+11)≤budget)
    (oneBits : (Cell.natural 1).bits≤budget) (nextBits : (Cell.natural (cursor+1)).bits≤budget)
    (endBits : (Cell.natural (cursor+2)).bits≤budget) (pcBits : natBits (before.pc+13)≤budget) :
    PrefixSafe input emitLeadCode before budget := by
  let a := loadSlotResult before base 15 .index
  let b := loadSlotResult a base 11 .old
  let c := writeCell b cursor (.rational q)
  let d := ({c with pc:=c.pc+1}).set .flag (.natural 1)
  let e := ({d with pc:=d.pc+1}).set .index (.natural (cursor+1))
  let f := writeCell e (cursor+1) (.rational weight)
  let g : State := {f with pc:=f.pc+1,output:=f.output++[f.register .old]}
  let h : State := {g with pc:=g.pc+1,output:=g.output++[g.register .value]}
  have pcSmall (offset : ℕ) (bounded : offset≤13) : natBits (before.pc+offset)≤budget :=
    (PDROC.DataBits.natBits_mono (Nat.add_le_add_left bounded before.pc)).trans pcBits
  have aRun : linearExecute input (loadSlot 15 .index) before=some a := loadSlot_execute input before base 15 .index fresh cursorLive
  have aSafe := PrefixSafe.loadSlot input before base 15 budget .index safe fresh cursorLive slot15Bits (pcSmall 3 (by decide))
  have aFresh : a.register .fresh=.natural base := by simp [a,loadSlotResult,fresh]
  have bRun : linearExecute input (loadSlot 11 .old) a=some b := loadSlot_execute input a base 11 .old aFresh qLive
  have bSafe := PrefixSafe.loadSlot input a base 11 budget .old (aSafe.final aRun) aFresh qLive slot11Bits
    (by simpa only [a,loadSlotResult,Nat.add_assoc] using pcSmall 6 (by decide))
  have cRun : linearExecute input [.store .index .old] b=some c := by
    simp [linearExecute,Instruction.execute,Cell.nat?,c,writeCell,b,a,loadSlotResult,cursorValue,qValue]
  have cSafe := PrefixSafe.store input b budget .index .old cursor (bSafe.final bRun)
    (by simp [b,a,loadSlotResult,cursorValue])
    (by simpa only [b,a,loadSlotResult,Nat.add_assoc] using pcSmall 7 (by decide))
  have dRun : linearExecute input [.constant .flag (.natural 1)] c=some d := rfl
  have dSafe := PrefixSafe.constant input c budget .flag (.natural 1) (cSafe.final cRun) oneBits
    (by simpa only [c,b,a,writeCell,loadSlotResult,Nat.add_assoc] using pcSmall 8 (by decide))
  have eRun : linearExecute input [.natOp .add .index .index .flag] d=some e := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,e,d,c,b,a,State.set,writeCell,loadSlotResult,cursorValue]
  have eSafe := PrefixSafe.natOp input d budget .add .index .index .flag cursor 1 (cursor+1) (dSafe.final dRun)
    (by simp [d,c,b,a,State.set,writeCell,loadSlotResult,cursorValue]) (by simp [d,State.set]) rfl nextBits
    (by simpa only [d,c,b,a,State.set,writeCell,loadSlotResult,Nat.add_assoc] using pcSmall 9 (by decide))
  have fRun : linearExecute input [.store .index .value] e=some f := by
    simp [linearExecute,Instruction.execute,Cell.nat?,f,e,d,c,b,a,State.set,writeCell,loadSlotResult,value]
  have fSafe := PrefixSafe.store input e budget .index .value (cursor+1) (eSafe.final eRun) (by simp [e,State.set])
    (by simpa only [e,d,c,b,a,State.set,writeCell,loadSlotResult,Nat.add_assoc] using pcSmall 10 (by decide))
  have gRun : linearExecute input [.output .old] f=some g := rfl
  have gSafe := output_sameBudget input f .old budget (fSafe.final fRun)
    (by simpa only [f,e,d,c,b,a,State.set,writeCell,loadSlotResult,Nat.add_assoc] using pcSmall 11 (by decide))
  have hRun : linearExecute input [.output .value] g=some h := rfl
  have hSafe := output_sameBudget input g .value budget (gSafe.final gRun)
    (by simpa only [g,f,e,d,c,b,a,State.set,writeCell,loadSlotResult,Nat.add_assoc] using pcSmall 12 (by decide))
  have lastSafe := PrefixSafe.natOp input h budget .add .index .index .flag (cursor+1) 1 (cursor+2) (hSafe.final hRun)
    (by simp [h,g,f,e,State.set,writeCell]) (by simp [h,g,f,e,d,State.set,writeCell])
    (by simp [NatOp.eval,Nat.add_assoc]) endBits
    (by simpa only [h,g,f,e,d,c,b,a,State.set,writeCell,loadSlotResult,Nat.add_assoc] using pcBits)
  let rest8 : List Instruction := [.natOp .add .index .index .flag]
  let rest7 : List Instruction := [.output .value]++rest8
  have safe7 : PrefixSafe input rest7 g budget := PrefixSafe.append input _ _ g h budget hRun hSafe lastSafe
  let rest6 : List Instruction := [.output .old]++rest7
  have safe6 : PrefixSafe input rest6 f budget := PrefixSafe.append input _ _ f g budget gRun gSafe safe7
  let rest5 : List Instruction := [.store .index .value]++rest6
  have safe5 : PrefixSafe input rest5 e budget := PrefixSafe.append input _ _ e f budget fRun fSafe safe6
  let rest4 : List Instruction := [.natOp .add .index .index .flag]++rest5
  have safe4 : PrefixSafe input rest4 d budget := PrefixSafe.append input _ _ d e budget eRun eSafe safe5
  let rest3 : List Instruction := [.constant .flag (.natural 1)]++rest4
  have safe3 : PrefixSafe input rest3 c budget := PrefixSafe.append input _ _ c d budget dRun dSafe safe4
  let rest2 : List Instruction := [.store .index .old]++rest3
  have safe2 : PrefixSafe input rest2 b budget := PrefixSafe.append input _ _ b c budget cRun cSafe safe3
  let rest1 : List Instruction := loadSlot 11 .old++rest2
  have safe1 : PrefixSafe input rest1 a budget := PrefixSafe.append input _ _ a b budget bRun bSafe safe2
  let rest0 : List Instruction := loadSlot 15 .index++rest1
  have all : PrefixSafe input rest0 before budget := PrefixSafe.append input _ _ before a budget aRun aSafe safe1
  simpa only [emitLeadCode,rest0,rest1,rest2,rest3,rest4,rest5,rest6,rest7,rest8,
    List.append_assoc,List.cons_append,List.nil_append] using all

theorem emit_prefix_safe (input : List Cell) (before : State) (base budget : ℕ) (header : Header) (weight : ℚ)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (value : before.register .value=.rational weight) (outside : base+16≤header.outputCursor) (safe : SafeBits before budget)
    (slot5Bits : 1+natBits (base+5)≤budget) (slot11Bits : 1+natBits (base+11)≤budget) (slot15Bits : 1+natBits (base+15)≤budget)
    (oneBits : (Cell.natural 1).bits≤budget) (nextBits : (Cell.natural (header.outputCursor+1)).bits≤budget)
    (endBits : (Cell.natural (header.outputCursor+2)).bits≤budget) (levelBits : (Cell.natural (header.level+1)).bits≤budget)
    (pcBits : natBits (before.pc+24)≤budget) : PrefixSafe input (basicBlock .emit).body before budget := by
  have cursor := represented.lookup (offset:=15) (value:=.natural header.outputCursor) rfl
  have q := represented.lookup (offset:=11) (value:=.rational header.q) rfl
  have level := represented.lookup (offset:=5) (value:=.natural header.level) rfl
  let d := emitLeadResult before base header.outputCursor header.q weight
  let e := storeSlotResult d base 15 .index
  have leadRun : linearExecute input emitLeadCode before=some d :=
    emitLead_execute input before base header.outputCursor header.q weight fresh value cursor.2 cursor.1 q.2 q.1
  have leadSafe := emitLead_prefix_safe input before base header.outputCursor budget header.q weight safe fresh value cursor.2 cursor.1 q.2 q.1
    slot15Bits slot11Bits oneBits nextBits endBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+13≤before.pc+24)).trans pcBits)
  have dFresh : d.register .fresh=.natural base := by simpa [d,emitLeadResult,loadSlotResult] using fresh
  have storeRun : linearExecute input (storeSlot 15 .index) d=some e := storeSlot_execute input d base 15 .index dFresh (by decide)
  have storeSafe := PrefixSafe.storeSlot input d base 15 budget .index (leadSafe.final leadRun) dFresh (by decide) slot15Bits
    (by simpa only [d,emitLeadResult,loadSlotResult,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+16≤before.pc+24)).trans pcBits))
  have eFresh : e.register .fresh=.natural base := by simp [e,storeSlotResult,dFresh]
  have eLive : base+5∈e.live := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem level.2))
  have eLevel : e.heap (base+5)=.natural header.level := by
    have first : base+5≠header.outputCursor := by omega
    have second : base+5≠header.outputCursor+1 := by omega
    simpa [e,d,storeSlotResult,emitLeadResult,loadSlotResult,first,second] using level.1
  have incrementSafe := increment_prefix_safe input e base 5 header.level budget (storeSafe.final storeRun) eFresh eLive eLevel slot5Bits oneBits levelBits
    (by simpa only [e,d,storeSlotResult,emitLeadResult,loadSlotResult,Nat.add_assoc] using pcBits)
  have tailSafe := PrefixSafe.append input (storeSlot 15 .index) (incrementSlot 5) d e budget storeRun storeSafe incrementSafe
  have all := PrefixSafe.append input emitLeadCode (storeSlot 15 .index++incrementSlot 5) before d budget leadRun leadSafe tailSafe
  simpa only [basicBlock,emitLeadCode,List.append_assoc] using all

theorem emit_bitSegment (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ) (header : Header) (weight : ℚ)
    (position : before.pc=labelAddress origin .emit) (represented : header.At before base)
    (fresh : before.register .fresh=.natural base) (value : before.register .value=.rational weight)
    (outside : base+16≤header.outputCursor) (safe : SafeBits before budget)
    (slot5Bits : 1+natBits (base+5)≤budget) (slot11Bits : 1+natBits (base+11)≤budget) (slot15Bits : 1+natBits (base+15)≤budget)
    (oneBits : (Cell.natural 1).bits≤budget) (nextBits : (Cell.natural (header.outputCursor+1)).bits≤budget)
    (endBits : (Cell.natural (header.outputCursor+2)).bits≤budget) (levelBits : (Cell.natural (header.level+1)).bits≤budget)
    (pcBits : natBits (before.pc+24)≤budget) (targetBits : natBits (labelAddress origin .levelGate)≤budget) :
    BitSegment origin input before
      {(emitResult before base header.outputCursor header.level header.q weight) with pc:=labelAddress origin .levelGate} 390 budget := by
  let middle := emitResult before base header.outputCursor header.level header.q weight
  let after : State := {middle with pc:=labelAddress origin .levelGate}
  have body := emit_execute input before base header weight represented fresh value outside
  have prefixes := emit_prefix_safe input before base budget header weight represented fresh value outside safe slot5Bits slot11Bits slot15Bits
    oneBits nextBits endBits levelBits pcBits
  have control : (controlInstruction origin (basicBlock .emit).control).execute input middle=some after := rfl
  exact BitSegment.ofBlock origin .emit input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed) ((prefixes.final body).withPC _ targetBits)

theorem emit_caller_bits (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma : ℕ) (input : List Cell)
    (initialCaller before : State) (header : Header) (weight : ℚ)
    (arguments : CallArguments P base endpoints returnPC initialCaller) (initialSafe : SafeBits initialCaller callerBudget)
    (position : before.pc=labelAddress origin .emit) (represented : header.At before base)
    (fresh : before.register .fresh=.natural base) (value : before.register .value=.rational weight)
    (outside : base+16≤header.outputCursor) (safe : SafeBits before (calleeOperandBudget P origin callerBudget Lgamma))
    (levelBound : header.level≤P.certificate.M+1)
    (cursorEnd : header.outputCursor+2≤calleeNaturalCap base endpoints returnPC P.certificate.M P.certificate.Q) :
    BitSegment origin input before
      {(emitResult before base header.outputCursor header.level header.q weight) with pc:=labelAddress origin .levelGate} 390
      (calleeOperandBudget P origin callerBudget Lgamma) := by
  let budget := calleeOperandBudget P origin callerBudget Lgamma
  have control := calleeOperandBudget_control P origin base endpoints returnPC callerBudget Lgamma initialCaller arguments initialSafe
  have nextBits := calleeOperandBudget_natural P origin base endpoints returnPC callerBudget Lgamma (header.outputCursor+1)
    initialCaller arguments initialSafe (by omega)
  have endBits := calleeOperandBudget_natural P origin base endpoints returnPC callerBudget Lgamma (header.outputCursor+2)
    initialCaller arguments initialSafe cursorEnd
  have levelBits := calleeOperandBudget_natural P origin base endpoints returnPC callerBudget Lgamma (header.level+1)
    initialCaller arguments initialSafe (by unfold calleeNaturalCap;omega)
  exact emit_bitSegment origin input before base budget header weight position represented fresh value outside safe
    (ControlBudget.slot P origin base budget 5 control (by decide)) (ControlBudget.slot P origin base budget 11 control (by decide))
    (ControlBudget.slot P origin base budget 15 control (by decide)) (ControlBudget.literal P origin base budget 1 control (by decide))
    nextBits endBits levelBits (ControlBudget.pc_prefix P origin base budget control before .emit 24 position (by decide))
    (ControlBudget.pc_target P origin base budget control .levelGate)

end PDLower.CalibrationCompute
