module

public import Paid.RootD27Core_HeapSolverArguments_017
public import Paid.RootD27Core_SolverDispatch_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame

def solverHeapDispatchCode (useLambda : Bool) (returnPC entryPC : ℕ) : List Instruction :=
  solverHeapArgumentsCode useLambda returnPC++[.jump entryPC]

/-- Genuine dispatch reaches the common solver entry with the source's
initial0 or Lambda request. All parameters are loaded from the actual prepared heap, keeping original input. The setup trace contains no fake entry, and
the final state is produced by the actual original .jump instruction. -/
theorem solverHeapDispatch_actual (P : Parameters) (fee : ℚ) (program : Program) (labels : RoutineLabels)
    (input : List Cell) (before : State) (useLambda : Bool) (returnPC : ℕ)
    (prepared : PDCompute.Solver.HeapList before 0 (preparedInput P fee))
    (fetched : FetchesCode program before.pc (solverHeapDispatchCode useLambda returnPC labels.solveEntry))
    (separatePC : before.pc+(solverHeapArgumentsCode useLambda returnPC).length<labels.solveEntry) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤270 ∧ after.pc=labels.solveEntry ∧
      after.register .fresh=.natural (99+2*P.certificate.M) ∧
      after.register .old=.natural returnPC ∧ after.register .address=.natural 96 ∧
      after.register .index=.natural P.certificate.stages ∧ after.register .value=.natural P.tools ∧
      after.register .flag=.rational fee ∧ after.register .total=.rational (initialPenalty P useLambda) ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output ∧
      actualSolveRequests labels trace=[initialPenalty P useLambda] ∧ entryCount labels.solveEntry trace=1 := by
  let middle:=solverArgumentsResult P fee before useLambda returnPC
  let after : State:={middle with pc:=labels.solveEntry}
  change FetchesCode program before.pc (solverHeapArgumentsCode useLambda returnPC++[.jump labels.solveEntry]) at fetched
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input
    (solverHeapArgumentsCode useLambda returnPC) (solverHeapArguments_straight useLambda returnPC)
    before middle fetched.append_left (solverHeapArguments_execute P fee input before useLambda returnPC prepared)
  have middlePC : middle.pc=before.pc+(solverHeapArgumentsCode useLambda returnPC).length := by
    rw [solverHeapArguments_length]
    rfl
  have beforeEntry : ∀ state∈trace,state.pc<labels.solveEntry := by
    intro state member
    have split:=List.dropLast_append_getLast? middle (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,inside,executed⟩:=prefixes state proper
      have straight : StraightCode ((solverHeapArgumentsCode useLambda returnPC).take count) :=
        fun instruction member => solverHeapArguments_straight useLambda returnPC instruction (List.mem_of_mem_take member)
      have pc:=linearExecute_pc input _ straight before state executed
      simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt inside)] at pc
      omega
    · have same : state=middle := by simpa only [List.mem_singleton] using terminal
      subst state
      rw [middlePC]
      exact separatePC
  have noneBefore:=no_solve_entry labels trace (fun state member => Nat.ne_of_lt (beforeEntry state member))
  have jump : program[middle.pc]?=some (.jump labels.solveEntry) := by
    rw [middlePC]
    exact (fetched (solverHeapArgumentsCode useLambda returnPC).length (by simp)).trans (by simp)
  have control : step program input middle=some after := by
    simp only [step,jump]
    rfl
  have appended:=chain_append_control program input trace middle after chain last control
  have nonempty : trace≠[] := by intro same;simp only [same,List.head?_nil,reduceCtorEq] at head
  have one:=one_solve_entry labels after (initialPenalty P useLambda) rfl rfl
  refine ⟨trace++[after],after,?_,by simp,appended.1,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil trace nonempty] using head
  · have short : time program trace≤255 := by
      have length : (solverHeapArgumentsCode useLambda returnPC).length≤16 := by
        rw [solverHeapArguments_length]
        cases useLambda <;> decide
      exact cost.trans (by omega)
    exact appended.2.trans (by omega)
  · rw [solveRequests_append,noneBefore.1,one.1,List.nil_append]
  · rw [solveEntries_append,noneBefore.2,one.2]

end RootD27.Core
