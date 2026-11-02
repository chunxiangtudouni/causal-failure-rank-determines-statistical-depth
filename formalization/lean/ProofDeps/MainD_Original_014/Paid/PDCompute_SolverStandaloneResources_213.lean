module

public import Paid.PDCompute_SolverStandalone_149
public import Paid.PDCompute_SolverCallerBits_210
public import Paid.PDCompute_SolverStandaloneCaps_212
public import Paid.PDCompute_SolverEmitLoopBits_209

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
attribute [local irreducible] fullCellCode cellFieldsCode matrixCode matrixPackCode solverCalleeCode solverOutputOrigin

/-- ONE original parameterless standalone solver, including actual input
loads, all matrix computation, original4/6 serialization, physical output
and fetched HALT. ONE witness satisfies every functional/time/space/bit
guarantee. The closed constant is chosen before ALL original inputs. -/
theorem solver_standalone_resources (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    ∃ trace : List State,∃ final : State,
      Runs solverStandaloneProgram (solveInput P fee penalty n k) trace final ∧
      final.output=encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n) ∧
      time solverStandaloneProgram trace≤40000*(P.certificate.M+1)*entryCount n k ∧
      peakCells trace≤128*entryCount n k ∧
      peakOperandBits trace≤solverStandaloneBitConstant*solverBitScale P fee penalty n k ∧
      ∀ state∈trace,RootD27.Bits.SafeBits state (solverStandaloneBitConstant*solverBitScale P fee penalty n k) := by
  let input:=solveInput P fee penalty n k
  let loaded:=solverInputResult initial solverOutputOrigin n k fee penalty
  let budget:=solverStandaloneBitConstant*solverBitScale P fee penalty n k
  have loaderUniform:=solver_loader_budget_uniform P fee penalty n k
  have calleeUniform:=solver_standalone_budget_uniform P fee penalty n k
  have guards:=solver_loader_budget_guards P fee penalty n k
  have small : 4≤budget:=guards.1.trans loaderUniform
  have initialSafe:=PDCompute.Pack.safeBits_mono solver_initial_safe (by omega : 2≤budget)
  obtain ⟨loader,loaderHead,loaderLast,loaderChain,loaderTime,loaderResources⟩:=
    solverInput_trace_bits P fee penalty n k solverOutputOrigin budget solverStandaloneProgram initial initialSafe small
      (guards.2.1.trans loaderUniform) (guards.2.2.1.trans loaderUniform) (guards.2.2.2.1.trans loaderUniform)
      (guards.2.2.2.2.1.trans loaderUniform) (guards.2.2.2.2.2.1.trans loaderUniform) (guards.2.2.2.2.2.2.trans loaderUniform)
      solverStandalone_input_fetch
  obtain ⟨callee,middle,calleeHead,calleeLast,calleeChain,calleeTime,returned,calleeMemory,_,_,calleeSafe,_,_,_⟩:=
    solver_callee_resources_in_program .inputROM solverStandaloneProgram input 11 solverStandalone_callee_fetch P fee penalty loaded
      0 n k 5 solverOutputOrigin rfl rfl rfl rfl rfl rfl rfl rfl (solverInput_endpointSource P fee penalty n k loaded) True.intro
  obtain ⟨middlePC,_middleBase,_middleOld,middleAddress,middleIndex,middleHeap,middleOutput,_middleFrame⟩:=returned
  let cells:=encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)
  have middleSafe:=PDCompute.Pack.safeBits_mono (calleeSafe middle (List.mem_of_getLast? calleeLast)) calleeUniform
  have oneBits : (.natural 1 : Cell).bits≤budget := by
    have one : (.natural 1 : Cell).bits=2 := by decide
    rw [one]
    omega
  have pointerBits : 1+natBits (resultBase 0 n k+cells.length)≤budget:=
    (solver_standalone_pointer_bits P fee penalty n k).trans calleeUniform
  have haltBits : natBits solverHaltPC≤budget := (solver_standalone_emit_pc P fee penalty n k).trans calleeUniform
  obtain ⟨emitted,final,emitHead,emitLast,emitChain,emitTime,finalPC,_,_,_,_,finalOutput,emitPrefix,emitSafe⟩:=
    emitHeap_trace_resources solverStandaloneProgram input solverOutputOrigin solverHaltPC budget solverStandalone_emit_fetch cells middle
      (resultBase 0 n k) middlePC middleAddress middleIndex middleHeap middleSafe oneBits pointerBits haltBits haltBits
  have first:=joinTrace_spec solverStandaloneProgram input loader callee initial loaded middle 180
    (38000*(P.certificate.M+1)*entryCount n k+15) loaderHead loaderLast calleeHead calleeLast loaderChain calleeChain loaderTime calleeTime
  have joined:=joinTrace_spec solverStandaloneProgram input (joinTrace loader callee) emitted initial middle final
    (180+(38000*(P.certificate.M+1)*entryCount n k+15)) (135*cells.length+30)
    first.1 first.2.1 emitHead emitLast first.2.2.1 emitChain first.2.2.2 emitTime
  have size : cells.length≤8*entryCount n k:=solver_original_encoding_length P fee penalty n k
  have entries : 1≤entryCount n k := by unfold entryCount;nlinarith
  have product : 1≤(P.certificate.M+1)*entryCount n k := by nlinarith [Nat.zero_le (P.certificate.M*entryCount n k)]
  have loadWorking : workingCells loaded=7:=rfl
  have middleWorking : workingCells middle≤7+62*entryCount n k := by
    have actual:=(calleeMemory middle (List.mem_of_getLast? calleeLast)).workspace_workingCells
    simpa only [loadWorking] using actual
  have allSpace : ∀ state∈joinTrace (joinTrace loader callee) emitted,workingCells state≤128*entryCount n k := by
    intro state member
    rcases RootD27.Core.joinTrace_member member with earlier|outputting
    · rcases RootD27.Core.joinTrace_member earlier with loading|computing
      · have unchanged:=loaderResources state loading
        have same : workingCells state=7 := by simp only [workingCells,unchanged.2.1,unchanged.2.2.1];rfl
        omega
      · have actual:=(calleeMemory state computing).workspace_workingCells
        rw [loadWorking] at actual
        omega
    · have actual:=solver_emitted_workingCells (emitPrefix state outputting)
      omega
  have allSafe : ∀ state∈joinTrace (joinTrace loader callee) emitted,RootD27.Bits.SafeBits state budget:=
    PDCompute.Pack.joinTrace_invariant (joinTrace loader callee) emitted (fun state=>RootD27.Bits.SafeBits state budget)
      (PDCompute.Pack.joinTrace_invariant loader callee (fun state=>RootD27.Bits.SafeBits state budget)
        (fun state member=>(loaderResources state member).2.2.2)
        (fun state member=>PDCompute.Pack.safeBits_mono (calleeSafe state member) calleeUniform)) emitSafe
  refine ⟨joinTrace (joinTrace loader callee) emitted,final,
    solver_runs_of_actual_chain solverStandaloneProgram input _ final joined.1 joined.2.2.1 joined.2.1
      (by rw [finalPC];exact solverStandalone_halt_fetch),?_,?_,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,
      PDCompute.Pack.safeBits_peak _ budget allSafe,allSafe⟩
  · simpa only [middleOutput,loaded,solverInputResult,initial,List.nil_append] using finalOutput
  · calc
      _≤(180+(38000*(P.certificate.M+1)*entryCount n k+15))+(135*cells.length+30):=joined.2.2.2
      _≤40000*(P.certificate.M+1)*entryCount n k:=by nlinarith [Nat.zero_le (P.certificate.M*entryCount n k)]

end PDCompute.Solver
