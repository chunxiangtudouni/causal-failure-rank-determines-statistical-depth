module

public import Paid.PDCompute_SolverCallee_146
public import Paid.PDCompute_SolverInputLoader_092
public import Paid.RootD27Core_EmitLoop_005
public import Paid.RootD27Core_EndpointRoute_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame

attribute [local irreducible] fullCellCode matrixCode matrixPackCode solverCalleeCode

def solverOutputOrigin : ℕ := 11+(solverCalleeCode .inputROM 11).length
def solverHaltPC : ℕ := solverOutputOrigin+7

/-- ONE fixed standalone program, before ALL original inputs. Actual
ROM arguments, real solver, live-heap output loop and fetched HALT. -/
def solverStandaloneCode : List Instruction :=
  solverInputCode solverOutputOrigin++(solverCalleeCode .inputROM 11++
    (RootD27.Core.emitHeapCode solverOutputOrigin solverHaltPC++[.halt]))

def solverStandaloneProgram : Program := solverStandaloneCode.toArray

theorem solverInputCode_length (returnPC : ℕ) : (solverInputCode returnPC).length=11 := rfl

theorem solverStandalone_input_fetch : FetchesCode solverStandaloneProgram 0 (solverInputCode solverOutputOrigin) :=
  (RootD27.Core.arrayLiteral_fetch solverStandaloneCode).append_left

theorem solverStandalone_callee_fetch : FetchesCode solverStandaloneProgram 11 (solverCalleeCode .inputROM 11) := by
  simpa only [solverStandaloneProgram,solverInputCode_length,Nat.zero_add] using
    (RootD27.Core.arrayLiteral_fetch solverStandaloneCode).append_right.append_left

theorem solverStandalone_emit_fetch :
    FetchesCode solverStandaloneProgram solverOutputOrigin (RootD27.Core.emitHeapCode solverOutputOrigin solverHaltPC) := by
  simpa only [solverStandaloneProgram,solverInputCode_length,Nat.zero_add,solverOutputOrigin] using
    (RootD27.Core.arrayLiteral_fetch solverStandaloneCode).append_right.append_right.append_left

theorem solverStandalone_halt_fetch : solverStandaloneProgram[solverHaltPC]?=some .halt := by
  have haltFetch := (RootD27.Core.arrayLiteral_fetch solverStandaloneCode).append_right.append_right.append_right
  have actual := haltFetch 0 (by decide)
  simpa only [solverStandaloneProgram,solverInputCode_length,Nat.zero_add,RootD27.Core.emitHeap_length,Nat.add_zero,solverHaltPC,solverOutputOrigin,List.getElem?_cons_zero] using actual

theorem solver_original_encoding_length (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ) (n k : ℕ) :
    (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)).length ≤ 8*entryCount n k := by
  have capacity:=PDCompute.Pack.encoding_capacity (P.cachedSolveMenuTable P.endpointCache fee penalty k n) n k
    (originalTable_rows P fee penalty n k) (originalTable_columns P fee penalty n k)
  have bound : resultCapacity n k ≤ 8*entryCount n k := by unfold resultCapacity entryCount; nlinarith
  exact capacity.trans bound

theorem solver_emitted_workingCells {before state : State} {cells : List Cell}
    (emitted : RootD27.Core.EmittedPrefix before cells state) : workingCells state ≤ workingCells before+cells.length := by
  obtain ⟨heap,live,written,pending,decomposition,output⟩:=emitted
  have lengths:=congrArg List.length decomposition
  simp only [List.length_append] at lengths
  simp only [workingCells,live,output,List.length_append]
  omega

end PDCompute.Solver
