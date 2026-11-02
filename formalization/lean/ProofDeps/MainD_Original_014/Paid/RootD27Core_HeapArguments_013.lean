module

public import Paid.RootD27Core_Arguments_001
public import Paid.RootD27Endpoint_CalleeFrame_026

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot)

/-- The raw-input continuation reads the thirteen prepared cells from
REAL live heap0..12. The original readonly input remains unchanged. -/
def endpointHeapArgumentsCode (base cache returnPC : ℕ) : List Instruction :=
  [.constant .fresh (.natural 0)]++loadSlot 7 .index++loadSlot 2 .total++loadSlot 4 .value++
    [.constant .address (.natural cache),.constant .old (.natural returnPC),.constant .fresh (.natural base)]

def endpointHeapArgumentsResult (P : Parameters) (before : State) (base cache returnPC : ℕ) : State :=
  {endpointArgumentsResult P before base cache returnPC with pc:=before.pc+13}

theorem endpointHeapArguments_length (base cache returnPC : ℕ) :
    (endpointHeapArgumentsCode base cache returnPC).length=13 := rfl

theorem endpointHeapArguments_straight (base cache returnPC : ℕ) :
    StraightCode (endpointHeapArgumentsCode base cache returnPC) := by
  simp [StraightCode,endpointHeapArgumentsCode,loadSlot,StraightInstruction]

theorem endpointHeapArguments_execute (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (base cache returnPC : ℕ)
    (prepared : HeapList before 0 (preparedInput P fee)) :
    linearExecute input (endpointHeapArgumentsCode base cache returnPC) before=
      some (endpointHeapArgumentsResult P before base cache returnPC) := by
  have mlive : 7∈before.live := prepared.1 7 (by change 7<13; decide)
  have glive : 2∈before.live := prepared.1 2 (by change 2<13; decide)
  have flive : 4∈before.live := prepared.1 4 (by change 4<13; decide)
  have m:=PDLower.CalibrationCompute.HeapList.value prepared 7 (by change 7<13; decide)
  have g:=PDLower.CalibrationCompute.HeapList.value prepared 2 (by change 2<13; decide)
  have f:=PDLower.CalibrationCompute.HeapList.value prepared 4 (by change 4<13; decide)
  change before.heap 7=.natural P.certificate.M at m
  change before.heap 2=.rational P.certificate.gamma at g
  change before.heap 4=.rational P.reviewFee at f
  simp [endpointHeapArgumentsCode,endpointHeapArgumentsResult,endpointArgumentsResult,loadSlot,
    linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,mlive,glive,flive,m,g,f,Nat.add_assoc]
  all_goals
    funext register
    cases register <;> simp

theorem endpoint_heap_budget (m : ℕ) : 210+7000*(m+1)≤7210*(m+1) := by omega

/-- No readonly-input replacement: actual live-heap argument reads and
the SAME framed endpoint callee compute the original cache while keeping
all13 genuine prepared cells, for any original readonly input. -/
theorem endpoint_from_prepared_heap_actual (P : Parameters) (fee : ℚ) (input : List Cell) (program : Program)
    (before : State) (base cache returnPC : ℕ)
    (prepared : HeapList before 0 (preparedInput P fee)) (below : 13≤base) (separated : base+48≤cache)
    (setup : FetchesCode program before.pc (endpointHeapArgumentsCode base cache returnPC))
    (callee : FetchesCode program (before.pc+13) (RootD27.Endpoint.endpointCode (before.pc+13))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤7210*(P.certificate.M+1) ∧ after.pc=returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural cache ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      HeapList after cache (encodeList encodeEndpoint P.endpointCache.toList) ∧
      HeapList after 0 (preparedInput P fee) ∧ after.output=before.output := by
  let middle:=endpointHeapArgumentsResult P before base cache returnPC
  obtain ⟨setupTrace,sh,sl,sc,st,_⟩:=linearExecute_trace_time program input
    (endpointHeapArgumentsCode base cache returnPC) (endpointHeapArguments_straight base cache returnPC)
    before middle setup (endpointHeapArguments_execute P fee input before base cache returnPC prepared)
  have setupCost : time program setupTrace≤210 := st
  have retained : HeapList middle 0 (preparedInput P fee) := prepared
  obtain ⟨actualTrace,after,ah,al,ac,actualCost,pc,nextFresh,old,address,index,stored,output,frame⟩:=
    RootD27.Endpoint.endpoint_callee_actual_frame P program input (before.pc+13) middle base cache returnPC
      rfl rfl rfl rfl rfl rfl rfl separated callee
  have joined:=joinTrace_spec program input setupTrace actualTrace before middle after
    210 (7000*(P.certificate.M+1)) sh sl ah al sc ac setupCost actualCost
  refine ⟨joinTrace setupTrace actualTrace,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2.trans (endpoint_heap_budget P.certificate.M),pc,nextFresh,old,address,index,stored,?_,output⟩
  apply frame.heapList retained
  intro offset inside
  change offset<13 at inside
  omega

end RootD27.Core
