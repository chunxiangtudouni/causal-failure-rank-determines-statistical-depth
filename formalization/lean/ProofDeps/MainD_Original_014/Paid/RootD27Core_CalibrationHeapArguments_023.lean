module

public import Paid.RootD27Core_HeapSolverArguments_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

/-- The actual calibration workspace starts immediately after the real
endpoint cache. Its variable base is computed by instructions, never put
into code as an input-dependent constant. -/
def calibrationHeapArgumentsCode (returnPC : ℕ) : List Instruction :=
  solverHeapArgumentPrefix.take 6++
    [.constant .address (.natural 7),.load .total .address,
     .constant .address (.natural 9),.load .index .address,
     .constant .address (.natural 2),.load .value .address,
     .constant .address (.natural 96),.constant .old (.natural returnPC)]

def calibrationHeapArgumentsResult (P : Parameters) (before : State) (returnPC : ℕ) : State :=
  {calibrationArgumentsResult P before (99+2*P.certificate.M) 96 returnPC with pc:=before.pc+14}

theorem calibrationHeapArguments_length (returnPC : ℕ) :
    (calibrationHeapArgumentsCode returnPC).length=14 := rfl

theorem calibrationHeapArguments_straight (returnPC : ℕ) :
    StraightCode (calibrationHeapArgumentsCode returnPC) := by
  simp [StraightCode,calibrationHeapArgumentsCode,solverHeapArgumentPrefix,StraightInstruction]

theorem calibrationHeapArguments_execute (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (returnPC : ℕ) (prepared : HeapList before 0 (preparedInput P fee)) :
    linearExecute input (calibrationHeapArgumentsCode returnPC) before=
      some (calibrationHeapArgumentsResult P before returnPC) := by
  have mlive : 7∈before.live:=prepared.1 7 (by change 7<13;decide)
  have qlive : 9∈before.live:=prepared.1 9 (by change 9<13;decide)
  have glive : 2∈before.live:=prepared.1 2 (by change 2<13;decide)
  have hm:=PDLower.CalibrationCompute.HeapList.value prepared 7 (by change 7<13;decide)
  have hq:=PDLower.CalibrationCompute.HeapList.value prepared 9 (by change 9<13;decide)
  have hg:=PDLower.CalibrationCompute.HeapList.value prepared 2 (by change 2<13;decide)
  change before.heap 7=.natural P.certificate.M at hm
  change before.heap 9=.natural P.certificate.Q at hq
  change before.heap 2=.rational P.certificate.gamma at hg
  have arithmetic : P.certificate.M*2+99=99+2*P.certificate.M := by omega
  simp [calibrationHeapArgumentsCode,calibrationHeapArgumentsResult,calibrationArgumentsResult,
    solverHeapArgumentPrefix,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    mlive,qlive,glive,hm,hq,hg,arithmetic,Nat.add_assoc]
  all_goals
    funext register
    cases register <;> simp

/-- Every real prefix is readonly; arbitrary original input/output and
live caller workspace remain exactly the same. -/
theorem calibrationHeapArguments_prefix_memory (P : Parameters) (fee : ℚ) (input : List Cell)
    (before after : State) (returnPC count : ℕ) (prepared : HeapList before 0 (preparedInput P fee))
    (bound : count≤14)
    (actual : linearExecute input ((calibrationHeapArgumentsCode returnPC).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  have mlive : 7∈before.live:=prepared.1 7 (by change 7<13;decide)
  have qlive : 9∈before.live:=prepared.1 9 (by change 9<13;decide)
  have glive : 2∈before.live:=prepared.1 2 (by change 2<13;decide)
  have hm:=PDLower.CalibrationCompute.HeapList.value prepared 7 (by change 7<13;decide)
  have hq:=PDLower.CalibrationCompute.HeapList.value prepared 9 (by change 9<13;decide)
  have hg:=PDLower.CalibrationCompute.HeapList.value prepared 2 (by change 2<13;decide)
  change before.heap 7=.natural P.certificate.M at hm
  change before.heap 9=.natural P.certificate.Q at hq
  change before.heap 2=.rational P.certificate.gamma at hg
  interval_cases count <;>
    simp [calibrationHeapArgumentsCode,solverHeapArgumentPrefix,linearExecute,Instruction.execute,
      State.set,NatOp.eval,Cell.nat?,mlive,qlive,glive,hm,hq,hg] at actual <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

theorem calibrationHeapArguments_actual (P : Parameters) (fee : ℚ) (input : List Cell)
    (program : Program) (before : State) (returnPC : ℕ)
    (prepared : HeapList before 0 (preparedInput P fee))
    (fetched : FetchesCode program before.pc (calibrationHeapArgumentsCode returnPC)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (calibrationHeapArgumentsResult P before returnPC) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤225 ∧
      ∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
  have run:=calibrationHeapArguments_execute P fee input before returnPC prepared
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input
    (calibrationHeapArgumentsCode returnPC) (calibrationHeapArguments_straight returnPC)
      before _ fetched run
  refine ⟨trace,head,last,chain,cost,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (calibrationHeapArgumentsResult P before returnPC) (by rw [last];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|terminal
  · obtain ⟨count,bound,actual⟩:=prefixes state proper
    apply calibrationHeapArguments_prefix_memory P fee input before state returnPC count prepared
    · simpa only [calibrationHeapArguments_length] using bound.le
    · exact actual
  · have same : state=calibrationHeapArgumentsResult P before returnPC:=List.mem_singleton.mp terminal
    subst state
    exact ⟨rfl,rfl,rfl⟩

end RootD27.Core
