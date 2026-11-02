module

public import Paid.RootD27Endpoint_Callee_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

/-- Read the ORIGINAL preparedInput positions7=M,2=gamma,4=reviewFee.
The only program parameters are static code/heap addresses, never P or
an endpoint answer. -/
def endpointArgumentsCode (base cache returnPC : ℕ) : List Instruction :=
  [.constant .address (.natural 7),.loadInput .index .address,
   .constant .address (.natural 2),.loadInput .total .address,
   .constant .address (.natural 4),.loadInput .value .address,
   .constant .address (.natural cache),.constant .old (.natural returnPC),
   .constant .fresh (.natural base)]

def endpointArgumentsResult (P : Parameters) (before : State) (base cache returnPC : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update before.register .index (.natural P.certificate.M))
        .total (.rational P.certificate.gamma)) .value (.rational P.reviewFee))
        .address (.natural cache)) .old (.natural returnPC)) .fresh (.natural base)
    pc:=before.pc+9}

def calibrationArgumentsCode (base cache returnPC : ℕ) : List Instruction :=
  [.constant .address (.natural 7),.loadInput .total .address,
   .constant .address (.natural 9),.loadInput .index .address,
   .constant .address (.natural 2),.loadInput .value .address,
   .constant .address (.natural cache),.constant .old (.natural returnPC),
   .constant .fresh (.natural base)]

def calibrationArgumentsResult (P : Parameters) (before : State) (base cache returnPC : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update before.register .total (.natural P.certificate.M))
        .index (.natural P.certificate.Q)) .value (.rational P.certificate.gamma))
        .address (.natural cache)) .old (.natural returnPC)) .fresh (.natural base)
    pc:=before.pc+9}

theorem endpointArguments_length (base cache returnPC : ℕ) :
    (endpointArgumentsCode base cache returnPC).length=9 := rfl

theorem calibrationArguments_length (base cache returnPC : ℕ) :
    (calibrationArgumentsCode base cache returnPC).length=9 := rfl

theorem endpointArguments_straight (base cache returnPC : ℕ) :
    StraightCode (endpointArgumentsCode base cache returnPC) := by
  intro instruction member
  simp only [endpointArgumentsCode,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h <;> subst instruction <;> trivial

theorem calibrationArguments_straight (base cache returnPC : ℕ) :
    StraightCode (calibrationArgumentsCode base cache returnPC) := by
  intro instruction member
  simp only [calibrationArgumentsCode,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h <;> subst instruction <;> trivial

theorem endpointArguments_execute (P : Parameters) (fee : ℚ) (before : State) (base cache returnPC : ℕ) :
    linearExecute (preparedInput P fee) (endpointArgumentsCode base cache returnPC) before=
      some (endpointArgumentsResult P before base cache returnPC) := by
  have hm : (preparedInput P fee)[7]?=some (.natural P.certificate.M) := rfl
  have hg : (preparedInput P fee)[2]?=some (.rational P.certificate.gamma) := rfl
  have hf : (preparedInput P fee)[4]?=some (.rational P.reviewFee) := rfl
  simp [endpointArgumentsCode,endpointArgumentsResult,linearExecute,Instruction.execute,State.set,Cell.nat?,hm,hg,hf]
  all_goals
    funext register
    cases register <;> simp

theorem calibrationArguments_execute (P : Parameters) (fee : ℚ) (before : State) (base cache returnPC : ℕ) :
    linearExecute (preparedInput P fee) (calibrationArgumentsCode base cache returnPC) before=
      some (calibrationArgumentsResult P before base cache returnPC) := by
  have hm : (preparedInput P fee)[7]?=some (.natural P.certificate.M) := rfl
  have hq : (preparedInput P fee)[9]?=some (.natural P.certificate.Q) := rfl
  have hg : (preparedInput P fee)[2]?=some (.rational P.certificate.gamma) := rfl
  simp [calibrationArgumentsCode,calibrationArgumentsResult,linearExecute,Instruction.execute,State.set,Cell.nat?,hm,hq,hg]
  all_goals
    funext register
    cases register <;> simp

/-- No caller storage or output is changed at ANY actually executed
instruction prefix, including the final setup state. -/
theorem endpointArguments_prefix_storage (P : Parameters) (fee : ℚ) (before after : State)
    (base cache returnPC count : ℕ) (bound : count≤9)
    (executed : linearExecute (preparedInput P fee) ((endpointArgumentsCode base cache returnPC).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  have hm : (preparedInput P fee)[7]?=some (.natural P.certificate.M) := rfl
  have hg : (preparedInput P fee)[2]?=some (.rational P.certificate.gamma) := rfl
  have hf : (preparedInput P fee)[4]?=some (.rational P.reviewFee) := rfl
  interval_cases count <;>
    simp [endpointArgumentsCode,linearExecute,Instruction.execute,State.set,Cell.nat?,hm,hg,hf] at executed <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

theorem calibrationArguments_prefix_storage (P : Parameters) (fee : ℚ) (before after : State)
    (base cache returnPC count : ℕ) (bound : count≤9)
    (executed : linearExecute (preparedInput P fee) ((calibrationArgumentsCode base cache returnPC).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  have hm : (preparedInput P fee)[7]?=some (.natural P.certificate.M) := rfl
  have hq : (preparedInput P fee)[9]?=some (.natural P.certificate.Q) := rfl
  have hg : (preparedInput P fee)[2]?=some (.rational P.certificate.gamma) := rfl
  interval_cases count <;>
    simp [calibrationArgumentsCode,linearExecute,Instruction.execute,State.set,Cell.nat?,hm,hq,hg] at executed <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

end RootD27.Core
