module

public import Paid.RootD27Core_EndpointOutput_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

/-- Keep the live endpoint cache at96..98+2M, compute the actual solver
workspace base99+2M, and read n/k/fee from original preparedInput0/1/5.
Only the return label and the two source-mandated initial penalties are
static code choices. No table or endpoint answer is supplied by ROM. -/
def solverArgumentPrefix : List Instruction :=
  [.constant .address (.natural 7),.loadInput .fresh .address,
   .constant .address (.natural 2),.natOp .multiply .fresh .fresh .address,
   .constant .address (.natural 99),.natOp .add .fresh .fresh .address,
   .constant .address (.natural 0),.loadInput .index .address,
   .constant .address (.natural 1),.loadInput .value .address,
   .constant .address (.natural 5),.loadInput .flag .address]

def initialPenaltyCode : Bool → List Instruction
  | false => [.constant .total (.rational 0)]
  | true => [.constant .address (.natural 11),.loadInput .total .address]

def solverArgumentsCode (useLambda : Bool) (returnPC : ℕ) : List Instruction :=
  solverArgumentPrefix++initialPenaltyCode useLambda++
    [.constant .address (.natural 96),.constant .old (.natural returnPC)]

def initialPenalty (P : Parameters) (useLambda : Bool) : ℚ := if useLambda then P.Lambda else 0

def solverArgumentsResult (P : Parameters) (fee : ℚ) (before : State) (useLambda : Bool) (returnPC : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update before.register .fresh (.natural (99+2*P.certificate.M)))
        .index (.natural P.certificate.stages)) .value (.natural P.tools)) .flag (.rational fee))
        .total (.rational (initialPenalty P useLambda))) .address (.natural 96)) .old (.natural returnPC)
    pc:=before.pc+(if useLambda then 16 else 15)}

theorem solverArguments_length (useLambda : Bool) (returnPC : ℕ) :
    (solverArgumentsCode useLambda returnPC).length=(if useLambda then 16 else 15) := by
  cases useLambda <;> rfl

theorem solverArguments_straight (useLambda : Bool) (returnPC : ℕ) :
    StraightCode (solverArgumentsCode useLambda returnPC) := by
  cases useLambda <;>
    simp [StraightCode,solverArgumentsCode,solverArgumentPrefix,initialPenaltyCode,StraightInstruction]

theorem solverArguments_execute (P : Parameters) (fee : ℚ) (before : State) (useLambda : Bool) (returnPC : ℕ) :
    linearExecute (preparedInput P fee) (solverArgumentsCode useLambda returnPC) before=
      some (solverArgumentsResult P fee before useLambda returnPC) := by
  have hm : (preparedInput P fee)[7]?=some (.natural P.certificate.M) := rfl
  have hn : (preparedInput P fee)[0]?=some (.natural P.certificate.stages) := rfl
  have hk : (preparedInput P fee)[1]?=some (.natural P.tools) := rfl
  have hf : (preparedInput P fee)[5]?=some (.rational fee) := rfl
  have baseArithmetic : P.certificate.M*2+99=99+2*P.certificate.M := by omega
  cases useLambda with
  | false =>
    simp [solverArgumentsCode,solverArgumentPrefix,initialPenaltyCode,solverArgumentsResult,
      initialPenalty,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hm,hn,hk,hf,
      baseArithmetic,Nat.add_assoc]
    all_goals
      funext register
      cases register <;> simp
  | true =>
    have hl : (preparedInput P fee)[11]?=some (.rational P.Lambda) := rfl
    simp [solverArgumentsCode,solverArgumentPrefix,initialPenaltyCode,solverArgumentsResult,
      initialPenalty,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hm,hn,hk,hf,hl,
      baseArithmetic,Nat.add_assoc]
    all_goals
      funext register
      cases register <;> simp

end RootD27.Core
