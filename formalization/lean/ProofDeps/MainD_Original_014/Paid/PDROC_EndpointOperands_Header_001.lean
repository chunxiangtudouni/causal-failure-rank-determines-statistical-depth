module

public import Paid.PDROC_EndpointOperands_Base_001
public import Paid.PDCompute_SolverHeaderResources_140

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDROC.EndpointOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver RootD27.Bits PDMenu.ComputeFrame

/-- The ORIGINAL static prefix is sixteen argument stores, three padding
setup opcodes and the eighteen-op counted base-row code. The actual
padding execution has seven rounds, not merely thirty-seven steps. -/
theorem header_static_code_length (origin : ℕ) :
    (solverPrologue++RootD27.Endpoint.paddingSetup++baseRowCode (origin+19)).length=37 := rfl

/-- All six saved arguments are genuine OLD caller Cells. In particular
E/returnPC/gamma/M/fee need no fabricated fixed-width initializer value;
the caller's same B already controls their actual register payloads. -/
theorem header_savedArguments_safe (before : State) (budget : ℕ) (safe : SafeBits before budget) :
    ∀ value ∈ savedArguments before,value.bits ≤ budget := by
  intro value member
  simp only [savedArguments,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact safe.register _

/-- Reuses the frozen numerical producer140 itself, not a functional
success oracle. ONE actual original header trace carries Header, frame,
output, every-prefix RegionMemory and complete SAME-B stateCellBits.
No incoming header/live workspace or type/P-bound on old scratch is added.
The padding lead's fourth instruction is the baseRowCode first flag1;
loop execution starts at origin+20, so this shared instruction is not
duplicated. The original conservative time bound2460 is retained. -/
theorem header_initialization_sameBudget (program : Program) (input : List Cell) (P : Parameters)
    (origin base E returnPC budget : ℕ) (before : State)
    (position : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (callerSafe : SafeBits before budget) (bounds : ControlBudget P origin base E returnPC budget)
    (prologueFetch : FetchesCode program before.pc solverPrologue)
    (leadFetch : FetchesCode program (origin+16) RootD27.Endpoint.paddingLeadCode)
    (loopFetch : FetchesCode program (origin+19) (baseRowCode (origin+19))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace ≤ 2460 ∧
      PDCompute.Solver.Header after base (initializedHeaderValues (solverPrologueResult before base) base) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+37 ∧
      PDCompute.Solver.Frame before after base 0 0 ∧ after.output=before.output ∧
      (∀ state ∈ trace,RegionMemory before state (cellRegion base headerWords) ∧ SafeBits state budget ∧
        origin ≤ state.pc ∧ state.pc ≤ origin+37) ∧
      ∀ state ∈ trace.dropLast,origin ≤ state.pc ∧ state.pc < origin+37 :=
  solver_header_initialization_resources program input origin before base 0 0 budget position fresh callerSafe
    (ControlBudget.headerAddress P origin base E returnPC budget bounds)
    (ControlBudget.zeroRat P origin base E returnPC budget bounds)
    (ControlBudget.pc P origin base E returnPC budget (origin+37) bounds (by unfold pcCap; omega))
    prologueFetch leadFetch loopFetch

end PDROC.EndpointOperands
