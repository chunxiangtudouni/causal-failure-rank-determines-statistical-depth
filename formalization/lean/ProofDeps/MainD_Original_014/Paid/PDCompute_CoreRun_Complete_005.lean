module
public import Paid.PDCompute_CoreRun_Join_003
public import PaperProofs.Paid.PDCompute_Codec_001
public import Paid.PDLower_CalibrationCompute_Standalone_081

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
@[expose] public section
namespace PDCompute.CoreRun.Generic
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

attribute [local irreducible] matrixCode solverCalleeCode PDLower.CalibrationCompute.kernel
  PDCompute.CorePrelude.program PDCompute.CorePrelude.bodyStart PDCompute.CorePrelude.afterCalibration
  initializeSearchCode bisectionBodyCode finalizationCode PDCompute.CoreSearchLoop.code
  PDCompute.CoreProgram.program PDCompute.CoreProgram.suffix PDCompute.CoreProgram.calleeCode
  PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.solveEntry PDCompute.CoreProgram.solveReturn
  PDCompute.CoreProgram.labels PDCompute.CoreProgram.pcUpper

def bitFactor (upper : ℕ) : ℕ := 134217728+2*natBits upper+256

structure Joined (ram : Program) (labels : RoutineLabels) (P : Parameters) (fee : ℚ)
    (origin upper : ℕ) (earlierTrace : List State) (before : State) where
  trace : List State
  main : List State
  after : State
  joined : trace=joinTrace earlierTrace main
  mainHead : main.head?=some before
  mainLast : main.getLast?=some after
  mainLower : ∀ state∈main,origin≤state.pc
  run : Runs ram (preparedInput P fee) trace after
  output : after.output=encodeArtifact (buildArtifact P fee)
  decoded : decodeArtifact after.output=some (buildArtifact P fee)
  timeBound : time ram trace≤300000*sourceCoreScale P fee
  space : peakCells trace≤512*sourceRecordSpace P
  safe : ∀ state∈trace,RootD27.Bits.SafeBits state (PDCompute.CoreGlobalBudget.budget P fee upper)
  bits : peakOperandBits trace≤bitFactor upper*coreOperandBound P fee
  requests : actualSolveRequests labels trace=
    (P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2
  countExact : PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=
    (actualSolveRequests labels trace).length
  countBound : PaperProofs.Paid.Computation.entryCount labels.solveEntry trace≤P.bisectionBudget fee+2
  endpointCount : PaperProofs.Paid.Computation.entryCount labels.endpointEntry trace=
    PaperProofs.Paid.Computation.entryCount 52 earlierTrace
  calibrationCount : PaperProofs.Paid.Computation.entryCount labels.calibrationEntry trace=
    PaperProofs.Paid.Computation.entryCount 316 earlierTrace
  refinement : SolverCallRefinement ram labels P fee 40000 trace
  pc : after.pc=origin+944
  halt : ram[after.pc]?=some .halt
  stopped : step ram (preparedInput P fee) after=none

/-- Entire actual join proof over an ABSTRACT RAM and addresses. The
fixed ROM is substituted only after this kernel certificate is compiled. -/
theorem assemble (ram : Program) (labels : RoutineLabels) (P : Parameters) (fee : ℚ)
    (origin upper : ℕ) (earlierTrace : List State) (before : State)
    (head : earlierTrace.head?=some initial) (last : earlierTrace.getLast?=some before)
    (chain : earlierTrace.IsChain (fun first later=>step ram (preparedInput P fee) first=some later))
    (timeBound : time ram earlierTrace≤prefixCost P) (position : before.pc=origin)
    (frontOutput : before.output=encodeList encodeEndpoint P.endpointCache.toList++
      encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList)
    (frontSpace : peakCells earlierTrace≤150*(P.certificate.M+1))
    (safe : ∀ state∈earlierTrace,RootD27.Bits.SafeBits state (PDCompute.CoreGlobalBudget.budget P fee upper))
    (frontRequests : actualSolveRequests labels earlierTrace=[])
    (frontCount : PaperProofs.Paid.Computation.entryCount labels.solveEntry earlierTrace=0)
    (frontCalls : SolverCallRefinement ram labels P fee 40000 earlierTrace)
    (main : PDCompute.CoreSuffix.Result ram labels (preparedInput P fee) P fee origin upper before)
    (entryEnd : origin+945=labels.solveEntry) (earlier : 316<origin)
    (endpointLabel : labels.endpointEntry=52) (calibrationLabel : labels.calibrationEntry=316) :
    Nonempty (Joined ram labels P fee origin upper earlierTrace before) := by
  have joined:=joinTrace_spec ram (preparedInput P fee) earlierTrace main.trace initial before main.after
    (prefixCost P) (PDCompute.CoreSuffix.cost P fee) head last main.head main.last chain main.chain timeBound main.timeBound
  have prefixBound:=(workingCells_le_peak_of_member earlierTrace before (List.mem_of_getLast? last)).trans frontSpace
  have allSpace : ∀ state∈joinTrace earlierTrace main.trace,workingCells state≤512*sourceRecordSpace P := by
    intro state member
    have envelope:=original_core_space_envelope P
    rcases joinTrace_member member with early|later
    · have bound:=(workingCells_le_peak_of_member earlierTrace state early).trans frontSpace
      omega
    · have bound:=(workingCells_le_peak_of_member main.trace state later).trans main.space
      omega
  have allSafe:=PDCompute.Pack.joinTrace_invariant earlierTrace main.trace (fun state=>RootD27.Bits.SafeBits state
    (PDCompute.CoreGlobalBudget.budget P fee upper)) safe main.safe
  have costBound : prefixCost P+PDCompute.CoreSuffix.cost P fee≤300000*sourceCoreScale P fee := by
    simpa only [prefixCost,PDCompute.CoreSuffix.cost,PDCompute.CoreSuffix.searchCost,Nat.add_assoc]
      using original_core_time_envelope P fee
  have boundary : before.pc≠labels.solveEntry := by
    have pc:=position
    omega
  have requests:=requests_join labels earlierTrace main.trace before last boundary
  rw [frontRequests,main.requests,List.nil_append] at requests
  have calls:=refinement_join ram labels P fee 40000 earlierTrace main.trace before
    last main.head frontCalls main.refinement
  have count:=RootD27.Core.entryCount_join_ne labels.solveEntry earlierTrace main.trace before last boundary
  rw [frontCount,Nat.zero_add] at count
  have output : main.after.output=encodeArtifact (buildArtifact P fee) := by
    rw [main.output,frontOutput]
    exact artifact_stream P fee
  have earlyCount (entry : ℕ) (earlier : entry<origin) :
      PaperProofs.Paid.Computation.entryCount entry (joinTrace earlierTrace main.trace)=
        PaperProofs.Paid.Computation.entryCount entry earlierTrace := by
    rw [RootD27.Core.entryCount_join_ne entry earlierTrace main.trace before last (by have pc:=position;omega),
      main.no_earlier_entry entry earlier,Nat.add_zero]
  refine ⟨⟨joinTrace earlierTrace main.trace,main.trace,main.after,rfl,main.head,main.last,main.lower,
    PDLower.CalibrationCompute.runs_of_actual_chain _ _ _ _ joined.1 joined.2.2.1 joined.2.1 main.halt,
    output,?_,joined.2.2.2.trans costBound,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,
    allSafe,(PDCompute.Pack.safeBits_peak _ _ allSafe).trans (PDCompute.CoreGlobalBudget.budget_le_core P fee _),
    requests,entries_eq_requests _ _ _ _ 40000 _ calls,count.le.trans main.count,?_,?_,calls,main.pc,main.halt,main.stopped⟩⟩
  · rw [output]
    exact PDCompute.decodeArtifact_encode _
  · rw [endpointLabel]
    exact earlyCount 52 (by omega)
  · rw [calibrationLabel]
    exact earlyCount 316 earlier

end PDCompute.CoreRun.Generic
