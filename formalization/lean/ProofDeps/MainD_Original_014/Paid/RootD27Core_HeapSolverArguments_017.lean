module

public import Paid.RootD27Core_SolverArguments_008
public import Paid.RootD27Core_HeapArguments_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

def solverHeapArgumentPrefix : List Instruction :=
  [.constant .address (.natural 7),.load .fresh .address,
   .constant .address (.natural 2),.natOp .multiply .fresh .fresh .address,
   .constant .address (.natural 99),.natOp .add .fresh .fresh .address,
   .constant .address (.natural 0),.load .index .address,
   .constant .address (.natural 1),.load .value .address,
   .constant .address (.natural 5),.load .flag .address]

def initialHeapPenaltyCode : Bool → List Instruction
  | false => [.constant .total (.rational 0)]
  | true => [.constant .address (.natural 11),.load .total .address]

def solverHeapArgumentsCode (useLambda : Bool) (returnPC : ℕ) : List Instruction :=
  solverHeapArgumentPrefix++initialHeapPenaltyCode useLambda++
    [.constant .address (.natural 96),.constant .old (.natural returnPC)]

theorem solverHeapArguments_length (useLambda : Bool) (returnPC : ℕ) :
    (solverHeapArgumentsCode useLambda returnPC).length=(if useLambda then 16 else 15) := by
  cases useLambda <;> rfl

theorem solverHeapArguments_straight (useLambda : Bool) (returnPC : ℕ) :
    StraightCode (solverHeapArgumentsCode useLambda returnPC) := by
  cases useLambda <;>
    simp [StraightCode,solverHeapArgumentsCode,solverHeapArgumentPrefix,initialHeapPenaltyCode,StraightInstruction]

/-- All original solver parameters are really loaded from prepared heap
cells. No readonly input is changed after the original raw preprocessor. -/
theorem solverHeapArguments_execute (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (useLambda : Bool) (returnPC : ℕ)
    (prepared : HeapList before 0 (preparedInput P fee)) :
    linearExecute input (solverHeapArgumentsCode useLambda returnPC) before=
      some (solverArgumentsResult P fee before useLambda returnPC) := by
  have mlive : 7∈before.live := prepared.1 7 (by change 7<13; decide)
  have nlive : 0∈before.live := prepared.1 0 (by change 0<13; decide)
  have klive : 1∈before.live := prepared.1 1 (by change 1<13; decide)
  have flive : 5∈before.live := prepared.1 5 (by change 5<13; decide)
  have llive : 11∈before.live := prepared.1 11 (by change 11<13; decide)
  have hm:=PDLower.CalibrationCompute.HeapList.value prepared 7 (by change 7<13; decide)
  have hn:=PDLower.CalibrationCompute.HeapList.value prepared 0 (by change 0<13; decide)
  have hk:=PDLower.CalibrationCompute.HeapList.value prepared 1 (by change 1<13; decide)
  have hf:=PDLower.CalibrationCompute.HeapList.value prepared 5 (by change 5<13; decide)
  have hl:=PDLower.CalibrationCompute.HeapList.value prepared 11 (by change 11<13; decide)
  change before.heap 7=.natural P.certificate.M at hm
  change before.heap 0=.natural P.certificate.stages at hn
  change before.heap 1=.natural P.tools at hk
  change before.heap 5=.rational fee at hf
  change before.heap 11=.rational P.Lambda at hl
  have baseArithmetic : P.certificate.M*2+99=99+2*P.certificate.M := by omega
  cases useLambda <;>
    simp [solverHeapArgumentsCode,solverHeapArgumentPrefix,initialHeapPenaltyCode,
      solverArgumentsResult,initialPenalty,linearExecute,Instruction.execute,State.set,NatOp.eval,
      Cell.nat?,mlive,nlive,klive,flive,llive,hm,hn,hk,hf,hl,baseArithmetic,Nat.add_assoc]
  all_goals
    funext register
    cases register <;> simp

end RootD27.Core
