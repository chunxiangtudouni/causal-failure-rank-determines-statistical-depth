module

public import Paid.PDCompute_SolverMatrixPack_142
public import Paid.PDCompute_SolverHeaderResources_140
public import Paid.PDCompute_SolverCountResources_144
public import Paid.RootD27Endpoint_Fetch_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation PDMenu.ComputeFrame

attribute [local irreducible] fullCellCode matrixCode matrixPackCode

/-- SAME literal37-op generic argument saver and Header producer. -/
def solverHeaderCode (origin : ℕ) : List Instruction :=
  solverPrologue++(RootD27.Endpoint.paddingSetup++baseRowCode (origin+19))

theorem solverHeaderCode_length (origin : ℕ) : (solverHeaderCode origin).length=37 := by
  simp only [solverHeaderCode,List.length_append,solverPrologue_length,RootD27.Endpoint.paddingSetup_length,baseRowCode_length]

/-- Complete fixed solver: original Header37, actual cache-length9,
full nested DP, original4/6 serializer and real indirect return.
No paper parameter, dimension, source, fee or penalty enters the code. -/
def solverCalleeCode (mode : ReaderMode) (origin : ℕ) : List Instruction :=
  solverHeaderCode origin++(endpointCountHeaderCode mode++matrixPackCode mode (origin+46))

theorem solverCallee_prologue_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (solverCalleeCode mode origin)) : FetchesCode program origin solverPrologue :=
  fetch.append_left.append_left

theorem solverCallee_loop_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (solverCalleeCode mode origin)) :
    FetchesCode program (origin+19) (baseRowCode (origin+19)) := by
  simpa only [solverPrologue_length,RootD27.Endpoint.paddingSetup_length,Nat.add_assoc] using
    fetch.append_left.append_right.append_right

theorem solverCallee_lead_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (solverCalleeCode mode origin)) :
    FetchesCode program (origin+16) RootD27.Endpoint.paddingLeadCode := by
  have lead:=RootD27.Endpoint.fetch_take fetch.append_left.append_right 4
  have literal : (RootD27.Endpoint.paddingSetup++baseRowCode (origin+19)).take 4=RootD27.Endpoint.paddingLeadCode := rfl
  rw [literal] at lead
  simpa only [solverPrologue_length] using lead

theorem solverCallee_count_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (solverCalleeCode mode origin)) :
    FetchesCode program (origin+37) (endpointCountHeaderCode mode) := by
  simpa only [solverHeaderCode_length] using fetch.append_right.append_left

theorem solverCallee_matrixPack_fetch (mode : ReaderMode) (program : Program) (origin : ℕ)
    (fetch : FetchesCode program origin (solverCalleeCode mode origin)) :
    FetchesCode program (origin+46) (matrixPackCode mode (origin+46)) := by
  simpa only [solverHeaderCode_length,endpointCountHeaderCode_length,Nat.add_assoc] using fetch.append_right.append_right

theorem initializedHeaderValue_saved (before : State) (base slot : ℕ) (inside : slot<6) :
    initializedHeaderValues (solverPrologueResult before base) base slot=
      (savedArguments before)[slot]'(by change slot<6; exact inside) := by
  simp only [initializedHeaderValues,ite_eq_left inside]
  exact PDLower.CalibrationCompute.HeapList.value (solverPrologue_arguments before base) slot (by change slot<6; exact inside)

end PDCompute.Solver
