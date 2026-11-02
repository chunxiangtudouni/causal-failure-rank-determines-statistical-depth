module

public import Paid.PDCompute_SolverMemoryJoin_062

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

/-- VERIFIED original solveInput positions0=n,1=k,3=fee,4=penalty,
cache source5. No copied endpoint cache and no input-dependent code. -/
def solverInputCode (returnPC : ℕ) : List Instruction :=
  [.constant .address (.natural 0),.loadInput .index .address,
   .constant .address (.natural 1),.loadInput .value .address,
   .constant .address (.natural 3),.loadInput .flag .address,
   .constant .address (.natural 4),.loadInput .total .address,
   .constant .address (.natural 5),.constant .old (.natural returnPC),.constant .fresh (.natural 0)]

def solverInputResult (before : State) (returnPC n k : ℕ) (fee penalty : ℚ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update before.register .index (.natural n)) .value (.natural k))
        .flag (.rational fee)) .total (.rational penalty)) .address (.natural 5)) .old (.natural returnPC)) .fresh (.natural 0)
    pc:=before.pc+11}

theorem solverInputCode_straight (returnPC : ℕ) : StraightCode (solverInputCode returnPC) := by
  intro instruction member
  simp only [solverInputCode,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h <;> subst instruction <;> trivial

theorem solverInputCode_execute (P : Parameters) (fee penalty : ℚ) (n k returnPC : ℕ) (before : State) :
    linearExecute (solveInput P fee penalty n k) (solverInputCode returnPC) before=
      some (solverInputResult before returnPC n k fee penalty) := by
  have hn : (solveInput P fee penalty n k)[0]?=some (.natural n) := rfl
  have hk : (solveInput P fee penalty n k)[1]?=some (.natural k) := rfl
  have hf : (solveInput P fee penalty n k)[3]?=some (.rational fee) := rfl
  have hp : (solveInput P fee penalty n k)[4]?=some (.rational penalty) := rfl
  simp [solverInputCode,solverInputResult,linearExecute,Instruction.execute,State.set,Cell.nat?,hn,hk,hf,hp]
  all_goals
    funext register
    cases register <;> simp

theorem solverInputCode_prefix_storage (P : Parameters) (fee penalty : ℚ) (n k returnPC : ℕ)
    (before after : State) (count : ℕ) (bound : count ≤ 11)
    (execute : linearExecute (solveInput P fee penalty n k) ((solverInputCode returnPC).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  have hn : (solveInput P fee penalty n k)[0]?=some (.natural n) := rfl
  have hk : (solveInput P fee penalty n k)[1]?=some (.natural k) := rfl
  have hf : (solveInput P fee penalty n k)[3]?=some (.rational fee) := rfl
  have hp : (solveInput P fee penalty n k)[4]?=some (.rational penalty) := rfl
  interval_cases count <;>
    simp [solverInputCode,linearExecute,Instruction.execute,State.set,Cell.nat?,hn,hk,hf,hp] at execute <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

theorem solverInput_endpointSource (P : Parameters) (fee penalty : ℚ) (n k : ℕ) (state : State) :
    EndpointSource .inputROM (solveInput P fee penalty n k) P 5 state := by
  intro offset bound
  unfold solveInput
  rw [List.getElem?_append_right (by change 5 ≤ 5+offset; omega)]
  simp only [List.length_cons,List.length_nil,Nat.add_sub_cancel_left]

theorem solverInputResult_entry (P : Parameters) (fee penalty : ℚ) (n k returnPC : ℕ)
    (before : State) (empty : before.live=∅) :
    Entry .inputROM (solveInput P fee penalty n k) P fee penalty n k 0 5 returnPC
      (solverInputResult before returnPC n k fee penalty) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,solverInput_endpointSource P fee penalty n k _,?_⟩
  change Disjoint before.live (workspace 0 n k)
  simp [empty]

theorem solverInput_trace_storage (P : Parameters) (fee penalty : ℚ) (n k returnPC : ℕ)
    (program : Program) (before : State)
    (fetch : FetchesCode program before.pc (solverInputCode returnPC)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (solverInputResult before returnPC n k fee penalty) ∧
      trace.IsChain (fun first later => step program (solveInput P fee penalty n k) first=some later) ∧
      time program trace ≤ 180 ∧
      ∀ state ∈ trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output := by
  have run:=solverInputCode_execute P fee penalty n k returnPC before
  obtain ⟨trace,head,last,chain,timeBound,prefixes⟩:=linearExecute_trace_time program (solveInput P fee penalty n k)
    (solverInputCode returnPC) (solverInputCode_straight returnPC) before _ fetch run
  refine ⟨trace,head,last,chain,timeBound,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (solverInputResult before returnPC n k fee penalty) (by rw [last]; simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|final
  · obtain ⟨count,bound,execute⟩:=prefixes state proper
    exact solverInputCode_prefix_storage P fee penalty n k returnPC before state count (Nat.le_of_lt bound) execute
  · have same : state=solverInputResult before returnPC n k fee penalty := by simpa only [List.mem_singleton] using final
    subst state
    exact ⟨rfl,rfl,rfl⟩

end PDCompute.Solver
