module

public import Paid.PDCompute_SolverStandaloneCode_148

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame

attribute [local irreducible] fullCellCode matrixCode matrixPackCode solverCalleeCode

theorem solver_runs_of_actual_chain (program : Program) (input : List Cell) (trace : List State) (final : State)
    (head : trace.head?=some initial) (chain : trace.IsChain (fun first later=>step program input first=some later))
    (last : trace.getLast?=some final) (halt : program[final.pc]?=some .halt) : Runs program input trace final := by
  refine ⟨head,chain,last,halt,StateTransition.mem_eval.mpr ⟨?_,?_⟩⟩
  · have nonempty : trace≠[] := by intro empty; rw [empty] at head; cases head
    have reached:=List.relationReflTransGen_of_exists_isChain trace chain nonempty
    have first : trace.head nonempty=initial := by
      have actual:=List.head?_eq_some_head nonempty
      rw [head] at actual
      exact (Option.some.inj actual).symm
    have finalState : trace.getLast nonempty=final := by
      have actual:=List.getLast?_eq_getLast_of_ne_nil nonempty
      rw [last] at actual
      exact (Option.some.inj actual).symm
    simpa only [StateTransition.Reaches,first,finalState,Option.mem_def] using reached
  · simp [step,halt,Instruction.execute]

/-- ONE original fixed standalone solver, ALL arbitrary original n/k
and rational penalty. It really loads original solveInput, computes the
whole table, serializes the ORIGINAL4/6 format, outputs it and HALTs.
Global operandBits is a separate unfinished theorem, not an extra premise. -/
theorem solver_standalone (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    ∃ trace : List State,∃ final : State,
      Runs solverStandaloneProgram (solveInput P fee penalty n k) trace final ∧
      final.output=encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n) ∧
      time solverStandaloneProgram trace ≤ 40000*(P.certificate.M+1)*entryCount n k ∧
      peakCells trace ≤ 128*entryCount n k := by
  let input:=solveInput P fee penalty n k
  let loaded:=solverInputResult initial solverOutputOrigin n k fee penalty
  obtain ⟨loader,loaderHead,loaderLast,loaderChain,loaderTime,loaderMemory⟩:=solverInput_trace_storage P fee penalty n k solverOutputOrigin
    solverStandaloneProgram initial solverStandalone_input_fetch
  obtain ⟨callee,middle,calleeHead,calleeLast,calleeChain,calleeTime,returned,calleeMemory,_⟩:=
    solver_callee_trace .inputROM solverStandaloneProgram input 11 solverStandalone_callee_fetch P fee penalty loaded 0 n k 5 solverOutputOrigin
      rfl rfl rfl rfl rfl rfl rfl rfl (solverInput_endpointSource P fee penalty n k loaded) True.intro
  obtain ⟨middlePC,_middleBase,_middleOld,middleAddress,middleIndex,middleHeap,middleOutput,_middleFrame⟩:=returned
  let cells:=encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)
  obtain ⟨emitted,final,emitHead,emitLast,emitChain,emitTime,finalPC,_,_,_,_,finalOutput,emitPrefix⟩:=
    RootD27.Core.emitHeap_actual solverStandaloneProgram input solverOutputOrigin solverHaltPC solverStandalone_emit_fetch cells middle
      (resultBase 0 n k) middlePC middleAddress middleIndex middleHeap
  have first:=joinTrace_spec solverStandaloneProgram input loader callee initial loaded middle 180
    (38000*(P.certificate.M+1)*entryCount n k) loaderHead loaderLast calleeHead calleeLast loaderChain calleeChain loaderTime calleeTime
  have joined:=joinTrace_spec solverStandaloneProgram input (joinTrace loader callee) emitted initial middle final
    (180+38000*(P.certificate.M+1)*entryCount n k) (135*cells.length+30)
    first.1 first.2.1 emitHead emitLast first.2.2.1 emitChain first.2.2.2 emitTime
  have size : cells.length ≤ 8*entryCount n k := solver_original_encoding_length P fee penalty n k
  have entries : 1 ≤ entryCount n k := by unfold entryCount; nlinarith
  have product : 1 ≤ (P.certificate.M+1)*entryCount n k := by nlinarith [Nat.zero_le (P.certificate.M*entryCount n k)]
  have loadWorking : workingCells loaded=7 := rfl
  have middleWorking : workingCells middle ≤ 7+62*entryCount n k := by
    have actual:=(calleeMemory middle (List.mem_of_getLast? calleeLast)).workspace_workingCells
    simpa only [loadWorking] using actual
  have allSpace : ∀ state∈joinTrace (joinTrace loader callee) emitted,workingCells state ≤ 128*entryCount n k := by
    intro state member
    rcases RootD27.Core.joinTrace_member member with earlier|outputting
    · rcases RootD27.Core.joinTrace_member earlier with loading|computing
      · have unchanged:=loaderMemory state loading
        have same : workingCells state=7 := by simp only [workingCells,unchanged.2.1,unchanged.2.2]; rfl
        omega
      · have actual:=(calleeMemory state computing).workspace_workingCells
        rw [loadWorking] at actual
        omega
    · have actual:=solver_emitted_workingCells (emitPrefix state outputting)
      omega
  refine ⟨joinTrace (joinTrace loader callee) emitted,final,
    solver_runs_of_actual_chain solverStandaloneProgram input _ final joined.1 joined.2.2.1 joined.2.1
      (by rw [finalPC]; exact solverStandalone_halt_fetch),?_,?_,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace⟩
  · simpa only [middleOutput,loaded,solverInputResult,initial,List.nil_append] using finalOutput
  · calc
      _ ≤ (180+38000*(P.certificate.M+1)*entryCount n k)+(135*cells.length+30) := joined.2.2.2
      _ ≤ 40000*(P.certificate.M+1)*entryCount n k := by nlinarith [Nat.zero_le (P.certificate.M*entryCount n k)]

end PDCompute.Solver
