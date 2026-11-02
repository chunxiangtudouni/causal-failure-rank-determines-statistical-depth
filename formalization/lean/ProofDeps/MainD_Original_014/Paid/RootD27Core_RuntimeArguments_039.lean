module

public import Paid.RootD27Core_HeapSolverArguments_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver
open PDLower.CalibrationCompute (linearExecute)

/-- The middle penalty is already in the real total register. These
fourteen instructions load only the other original solver arguments;
the runtime penalty is neither inserted into code nor supplied by ROM. -/
def solverRuntimeArgumentsCode (returnPC : ℕ) : List Instruction :=
  solverHeapArgumentPrefix++
    [.constant .address (.natural 96),.constant .old (.natural returnPC)]

def solverRuntimeArgumentsResult (P : Parameters) (fee : ℚ) (before : State) (returnPC : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update before.register .fresh (.natural (99+2*P.certificate.M)))
        .index (.natural P.certificate.stages)) .value (.natural P.tools)) .flag (.rational fee))
        .address (.natural 96)) .old (.natural returnPC)
    pc:=before.pc+14}

def solverRuntimeDispatchCode (returnPC entryPC : ℕ) : List Instruction :=
  solverRuntimeArgumentsCode returnPC++[.jump entryPC]

theorem solverRuntimeArguments_length (returnPC : ℕ) :
    (solverRuntimeArgumentsCode returnPC).length=14 := rfl

theorem solverRuntimeArguments_straight (returnPC : ℕ) :
    StraightCode (solverRuntimeArgumentsCode returnPC) := by
  simp [StraightCode,solverRuntimeArgumentsCode,solverHeapArgumentPrefix,StraightInstruction]

theorem solverRuntimeArguments_execute (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (returnPC : ℕ) (prepared : HeapList before 0 (preparedInput P fee)) :
    linearExecute input (solverRuntimeArgumentsCode returnPC) before=
      some (solverRuntimeArgumentsResult P fee before returnPC) := by
  have mlive : 7∈before.live := prepared.1 7 (by change 7<13; decide)
  have nlive : 0∈before.live := prepared.1 0 (by change 0<13; decide)
  have klive : 1∈before.live := prepared.1 1 (by change 1<13; decide)
  have flive : 5∈before.live := prepared.1 5 (by change 5<13; decide)
  have hm:=PDLower.CalibrationCompute.HeapList.value prepared 7 (by change 7<13; decide)
  have hn:=PDLower.CalibrationCompute.HeapList.value prepared 0 (by change 0<13; decide)
  have hk:=PDLower.CalibrationCompute.HeapList.value prepared 1 (by change 1<13; decide)
  have hf:=PDLower.CalibrationCompute.HeapList.value prepared 5 (by change 5<13; decide)
  change before.heap 7=.natural P.certificate.M at hm
  change before.heap 0=.natural P.certificate.stages at hn
  change before.heap 1=.natural P.tools at hk
  change before.heap 5=.rational fee at hf
  have baseArithmetic : P.certificate.M*2+99=99+2*P.certificate.M := by omega
  simp [solverRuntimeArgumentsCode,solverHeapArgumentPrefix,solverRuntimeArgumentsResult,
    linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,mlive,nlive,klive,flive,
    hm,hn,hk,hf,baseArithmetic,Nat.add_assoc]
  all_goals
    funext register
    cases register <;> simp

end RootD27.Core
