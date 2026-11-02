module
public import Paid.PDCompute_CoreSuffix_Boundary_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
@[expose] public section
namespace PDCompute.CoreSuffix
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

structure InitialResult (program : Program) (labels : RoutineLabels) (input : List Cell)
    (P : Parameters) (fee : ℚ) (origin pcUpper : ℕ) (before : State) where
  trace : List State
  after : State
  head : trace.head?=some before
  last : trace.getLast?=some after
  chain : trace.IsChain (fun first later=>step program input first=some later)
  timeBound : time program trace≤85000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools
  pc : after.pc=origin+164
  ready : Ready P fee after
  represented : SearchStateRep P fee after (P.cachedInitialState P.endpointCache fee)
  counter : after.heap 28=.natural (P.bisectionBudget fee)
  output : after.output=before.output
  memory : ∀ state∈trace,RegionMemory before state (coreSearchRegion P)
  safe : ∀ state∈trace,RootD27.Bits.SafeBits state (PDCompute.CoreGlobalBudget.budget P fee pcUpper)
  space : peakCells trace≤workingCells before+156*PDCompute.Solver.entryCount P.certificate.stages P.tools
  requests : actualSolveRequests labels trace=[0,P.Lambda]
  count : PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=2
  refinement : SolverCallRefinement program labels P fee 40000 trace
  lower : ∀ state∈trace,origin≤state.pc

/-- No initialized search data or solved table is assumed. All internal
rooms are supplied by the original input's already fixed global B. -/
theorem initialize_actual (P : Parameters) (fee : ℚ) (program : Program) (labels : RoutineLabels)
    (input : List Cell) (origin pcUpper : ℕ) (before : State) (position : before.pc=origin)
    (ready : Ready P fee before)
    (safe : RootD27.Bits.SafeBits before (PDCompute.CoreGlobalBudget.budget P fee pcUpper))
    (endBound : origin+945≤pcUpper) (belowEntry : origin+945≤labels.solveEntry)
    (solverOrigin : labels.solveEntry+1≤pcUpper)
    (solverLength : (solverCalleeCode .liveHeap (labels.solveEntry+1)).length≤pcUpper)
    (markerLabel : labels.solveReturn=PDLower.CoreRuntimeNumeric.commonSolverMarkerPC labels)
    (fetched : FetchesCode program origin (initializeSearchCode origin labels.solveEntry))
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1))) :
    Nonempty (InitialResult program labels input P fee origin pcUpper before) := by
  have realFetch : FetchesCode program before.pc (initializeSearchCode before.pc labels.solveEntry) := by
    rw [position]
    exact fetched
  have solvers:=PDCompute.CoreGlobalBudget.budget_initial_solvers P fee pcUpper
  obtain ⟨trace,after,head,last,chain,cost,pc,fresh,header,represented,prepared,stored,counter,output,
    space,memory,requests,count,bits,_peakBits,refinement,scope,_proper,_firstExit⟩:=
    PDCompute.CoreInitialize.initialize_search_resources P fee program labels input before _ ready.header ready.fresh
      ready.prepared ready.cache realFetch (by omega) stubFetch bodyFetch _ safe
      (PDCompute.CoreGlobalBudget.budget_small P fee pcUpper)
      (PDCompute.CoreGlobalBudget.budget_runtime_natural P fee pcUpper _ (le_refl _))
      (PDCompute.CoreGlobalBudget.budget_pc_cell P fee pcUpper _ (by omega))
      (PDCompute.CoreGlobalBudget.budget_runtime_control P fee pcUpper _ solverOrigin solverLength)
      solvers.1 solvers.2 markerLabel
  refine ⟨⟨trace,after,head,last,chain,cost,by omega,⟨header,fresh,prepared,stored⟩,represented,counter,
    output,fun state member=>(memory state member).enlarge (initialization_subset P fee),bits,space,
    requests,count,refinement,?_⟩⟩
  intro state member
  rcases scope state member with inline|callee
  · omega
  · have bound:=callee.1
    omega

end PDCompute.CoreSuffix
