module

public import Paid.PDCompute_SolverCallerGivenBudget_217
public import Paid.PDLower_CoreRuntimeNumeric_ControlRoom_002
public import Paid.RootD27Core_SolverStub_011
public import Paid.RootD27Core_CalibrationCaller_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDLower.CoreRuntimeNumeric

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver PDCompute.NatControl RootD27.Core RootD27.Bits

/-- A transparent numerical control reference, independent of the actual
dirty caller. It carries only the fixed raw-derived solver base. -/
def controlAnchor (base : ℕ) : State := initial.set .fresh (.natural base)

def controlAnchorBits (base : ℕ) : ℕ := 2+(Cell.natural base).bits

def runtimeControlRoom (P : Parameters) (origin : ℕ) : ℕ :=
  controlAllowance (controlAnchorBits (99+2*P.certificate.M)) P.certificate.stages P.tools
    origin (solverCalleeCode .liveHeap origin).length

theorem controlAnchor_safe (base : ℕ) : SafeBits (controlAnchor base) (controlAnchorBits base) := by
  have safe : SafeBits initial (controlAnchorBits base) := by
    apply SafeBits.of_fields
    · intro target
      change (Cell.natural 0).bits≤2+(Cell.natural base).bits
      have small : (Cell.natural 0).bits=2 := by decide
      omega
    · intro location member
      simp [initial] at member
    · intro location member
      simp [initial] at member
    · intro value member
      simp only [initial,List.not_mem_nil] at member
    · change natBits 0≤2+(Cell.natural base).bits
      have small : natBits 0=1 := by decide
      omega
  exact safe.set .fresh (.natural base) (by unfold controlAnchorBits;omega)

theorem runtime_control_context (P : Parameters) (origin budget : ℕ)
    (room : runtimeControlRoom P origin≤budget) :
    SolverControlContext (controlAnchor (99+2*P.certificate.M)) (controlAnchorBits (99+2*P.certificate.M))
      (99+2*P.certificate.M) P.certificate.stages P.tools .liveHeap origin budget :=
  ⟨controlAnchor_safe _,by simp [controlAnchor,State.set],room⟩

/-- Pure original dimensions and static code geometry pay the control
reference once; arbitrary incoming scratch does not occur in this bound. -/
theorem runtime_control_room_le_core (P : Parameters) (fee : ℚ) (origin : ℕ) :
    runtimeControlRoom P origin≤64*coreOperandBound P fee+natBits origin+
      natBits (solverCalleeCode .liveHeap origin).length+64 := by
  have base := runtime_address_room_le_core P fee
  have baseLe := runtime_base_le_limit P
  have smaller := Nat.add_le_add_left (PDROC.DataBits.natBits_mono baseLe) 1
  have dimensions : natBits P.certificate.stages≤P.certificate.stages+1 :=
    Nat.add_le_add_right (Nat.log2_le_self _) 1
  have raw : natBits P.certificate.stages+natBits P.tools≤rawSize P fee := by unfold rawSize;omega
  have core : rawSize P fee≤coreOperandBound P fee := by unfold coreOperandBound;omega
  unfold runtimeControlRoom controlAllowance controlAnchorBits
  change 2+(1+natBits (99+2*P.certificate.M))+natBits P.certificate.stages+natBits P.tools+
    natBits origin+natBits (solverCalleeCode .liveHeap origin).length+32≤_
  change 1+natBits (runtimeAddressLimit P)≤32*coreOperandBound P fee at base
  omega

/-- Every proper PC comes from the actual common stub or the actual
217 callee, while all original return/table/memory/log facts use this
same joined witness. Incoming dirty scratch is paid separately. -/
theorem stub_resources (mode : ReaderMode) (program : Program) (input : List Cell)
    (labels : RoutineLabels) (P : Parameters) (fee penalty : ℚ) (before : State)
    (base n k source returnPC : ℕ)
    (position : before.pc=labels.solveEntry) (returnSeparate : returnPC≠labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode mode (labels.solveEntry+1)))
    (fresh : before.register .fresh=.natural base) (old : before.register .old=.natural returnPC)
    (address : before.register .address=.natural source) (total : before.register .total=.rational penalty)
    (index : before.register .index=.natural n) (value : before.register .value=.natural k)
    (flag : before.register .flag=.rational fee)
    (endpoint : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (controlCaller : State) (incoming budget : ℕ)
    (context : SolverControlContext controlCaller incoming base n k mode (labels.solveEntry+1) budget)
    (safe : SafeBits before budget) (scalarRoom : 4194304*solverBitScale P fee penalty n k≤budget)
    (indexBits : 1+natBits (P.certificate.M+1)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤38100*(P.certificate.M+1)*PDCompute.Solver.entryCount n k ∧
      Return P fee penalty n k base returnPC before after ∧
      (∀ state∈trace,RegionMemory before state (workspace base n k)) ∧
      peakCells trace≤workingCells before+62*PDCompute.Solver.entryCount n k ∧
      actualSolveRequests labels trace=[penalty] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 ∧
      DenseOriginalTable after P fee penalty base n k ∧
      PDLower.CalibrationCompute.HeapList after (cellBase base k n k)
        (denseEncodeEntry (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty k n) n k)) ∧
      (∀ state∈trace,SafeBits state budget) ∧
      (∀ state∈trace.dropLast,labels.solveEntry≤state.pc ∧
        state.pc<labels.solveEntry+1+(solverCalleeCode mode (labels.solveEntry+1)).length) := by
  let entered : State:={before with pc:=labels.solveEntry+1}
  have jump : step program input before=some entered := by
    simp only [step,position,stubFetch]
    rfl
  have stubChain : [before,entered].IsChain (fun first later=>step program input first=some later) :=
    List.isChain_cons_cons.mpr ⟨jump,.singleton entered⟩
  have stubTime : time program [before,entered]≤30:=time_le_length program [before,entered]
  have enteredSafe : SafeBits entered budget := safe.withPC _ (context.pc _ (by omega))
  obtain ⟨body,after,bh,bl,bc,bt,returned,memory,peak,_bitPeak,bodySafe,scope,dense,root⟩:=
    solver_callee_given_budget_in_program mode program input (labels.solveEntry+1) bodyFetch P fee penalty entered
      base n k source returnPC rfl fresh old address total index value flag endpoint avoids
      controlCaller incoming budget context enteredSafe scalarRoom indexBits sourceBits
  have bodyExcluded : ∀ state∈body,state.pc≠labels.solveEntry := by
    intro state member
    have split:=List.dropLast_append_getLast? after (by rw [bl];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · have lower:=(scope state proper).1
      omega
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      rw [returned.1]
      exact returnSeparate
  have noBody:=no_solve_entry labels body bodyExcluded
  have one:=one_solve_entry labels before penalty position total
  have joined:=joinTrace_spec program input [before,entered] body before entered after
    30 (38000*(P.certificate.M+1)*PDCompute.Solver.entryCount n k+15)
      rfl rfl bh bl stubChain bc stubTime bt
  change Return P fee penalty n k base returnPC before after at returned
  change ∀ state∈body,RegionMemory before state (workspace base n k) at memory
  change peakCells body≤workingCells before+62*PDCompute.Solver.entryCount n k at peak
  have allMemory : ∀ state∈joinTrace [before,entered] body,RegionMemory before state (workspace base n k) := by
    intro state member
    rcases joinTrace_member member with stubMember|bodyMember
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at stubMember
      rcases stubMember with same|same
      · subst state
        exact .refl before _
      · subst state
        exact .refl before _
    · exact memory state bodyMember
  have allSpace : ∀ state∈joinTrace [before,entered] body,
      workingCells state≤workingCells before+62*PDCompute.Solver.entryCount n k := by
    intro state member
    rcases joinTrace_member member with stubMember|bodyMember
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at stubMember
      rcases stubMember with same|same
      · subst state
        omega
      · subst state
        change workingCells before≤workingCells before+62*PDCompute.Solver.entryCount n k
        omega
    · exact (workingCells_le_peak_of_member body state bodyMember).trans peak
  have allSafe : ∀ state∈joinTrace [before,entered] body,SafeBits state budget :=
    PDCompute.Pack.joinTrace_invariant _ _ _ (by
      intro state member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with same|same
      · subst state;exact safe
      · subst state;exact enteredSafe) bodySafe
  have bodyNonempty : body≠[] := by intro empty;simp [empty] at bh
  have proper : ∀ state∈(joinTrace [before,entered] body).dropLast,
      labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode mode (labels.solveEntry+1)).length := by
    intro state member
    change state∈([before]++body).dropLast at member
    rw [List.dropLast_append_of_ne_nil bodyNonempty] at member
    rcases List.mem_append.mp member with stubMember|bodyMember
    · have same := List.mem_singleton.mp stubMember
      subst state
      rw [position]
      omega
    · have bounded := scope state bodyMember
      omega
  refine ⟨joinTrace [before,entered] body,after,joined.1,joined.2.1,joined.2.2.1,?_,returned,
    allMemory,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,?_,?_,dense,root,allSafe,proper⟩
  · have positive : 0<(P.certificate.M+1)*PDCompute.Solver.entryCount n k := by
      unfold PDCompute.Solver.entryCount
      positivity
    have budget : 30+(38000*(P.certificate.M+1)*PDCompute.Solver.entryCount n k+15)≤
        38100*(P.certificate.M+1)*PDCompute.Solver.entryCount n k := by
      simp only [Nat.mul_assoc]
      omega
    exact joined.2.2.2.trans budget
  · change actualSolveRequests labels ([before]++body)=[penalty]
    rw [solveRequests_append,one.1,noBody.1,List.append_nil]
  · change PaperProofs.Paid.Computation.entryCount labels.solveEntry ([before]++body)=1
    rw [solveEntries_append,one.2,noBody.2,Nat.add_zero]

end PDLower.CoreRuntimeNumeric
