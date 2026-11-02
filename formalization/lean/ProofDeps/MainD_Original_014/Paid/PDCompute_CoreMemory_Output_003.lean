module
public import Paid.PDCompute_CoreMemory_Layout_001
public import Paid.PDROC_D27Prepare_Output_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreMemory
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver

def outputBound (M n k : ℕ) : ℕ:=16*PDCompute.Solver.entryCount n k+4*M+10

theorem original_table_length_le (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)).length≤8*PDCompute.Solver.entryCount n k:=by
  simpa only [RootD27.Core.retainedTableCapacity] using
    (RootD27.Core.original_table_capacity P fee penalty n k).trans (RootD27.Core.retained_capacity_enough n k)

def StateTablesFit (n k : ℕ) : MultiplierState→Prop
  | .exact solution=>(encodeTable solution.table).length≤8*PDCompute.Solver.entryCount n k
  | .bracket lower upper=>(encodeTable lower.table).length≤8*PDCompute.Solver.entryCount n k ∧
      (encodeTable upper.table).length≤8*PDCompute.Solver.entryCount n k

theorem encodeState_length_le (n k : ℕ) (state : MultiplierState) (tables : StateTablesFit n k state) :
    (encodeState state).length≤16*PDCompute.Solver.entryCount n k+3:=by
  cases state with
  | exact solution =>
    change (encodeTable solution.table).length≤8*PDCompute.Solver.entryCount n k at tables
    simp only [encodeState,encodeSolve,List.length_cons]
    omega
  | bracket lower upper =>
    change (encodeTable lower.table).length≤8*PDCompute.Solver.entryCount n k ∧
      (encodeTable upper.table).length≤8*PDCompute.Solver.entryCount n k at tables
    simp only [encodeState,encodeSolve,List.length_cons,List.length_append]
    omega

theorem cached_initial_tables_fit (P : Parameters) (fee : ℚ) :
    StateTablesFit P.certificate.stages P.tools (P.cachedInitialState P.endpointCache fee):=
  ⟨original_table_length_le P fee 0 _ _,original_table_length_le P fee P.Lambda _ _⟩

theorem cached_bisect_tables_fit (P : Parameters) (fee : ℚ) (state : MultiplierState)
    (tables : StateTablesFit P.certificate.stages P.tools state) :
    StateTablesFit P.certificate.stages P.tools (P.cachedBisect P.endpointCache fee state):=by
  cases state with
  | exact solution =>exact tables
  | bracket lower upper =>
    have middle:=original_table_length_le P fee ((lower.multiplier+upper.multiplier)/2) P.certificate.stages P.tools
    dsimp only [cachedBisect]
    split_ifs
    · exact middle
    · exact ⟨middle,tables.2⟩
    · exact ⟨tables.1,middle⟩

theorem cached_step_tables_fit (P : Parameters) (fee : ℚ) (state : MultiplierState)
    (tables : StateTablesFit P.certificate.stages P.tools state) :
    StateTablesFit P.certificate.stages P.tools (P.cachedMultiplierStep P.endpointCache fee state):=by
  unfold cachedMultiplierStep
  split_ifs
  · exact tables
  · exact cached_bisect_tables_fit P fee state tables

theorem cached_search_tables_fit (P : Parameters) (fee : ℚ) (steps : ℕ) :
    StateTablesFit P.certificate.stages P.tools (P.cachedMultiplierSearch P.endpointCache fee steps):=by
  induction steps with
  | zero =>exact cached_initial_tables_fit P fee
  | succ steps ih =>exact cached_step_tables_fit P fee _ ih

/-- At most TWO original tables occur in encodeState, independently of
the number of real solver calls used to construct the final state. -/
theorem encodeArtifact_length_le_of_tables (P : Parameters) (frontend : CachedFrontend) (weight : ℚ)
    (endpoints : frontend.endpoints=P.endpointCache)
    (calibration : frontend.calibrationWeights=P.calibrationWeightCache P.endpointCache)
    (tables : StateTablesFit P.certificate.stages P.tools frontend.state) :
    (encodeArtifact ⟨frontend,weight⟩).length≤outputBound P.certificate.M P.certificate.stages P.tools:=by
  have stateLength:=encodeState_length_le P.certificate.stages P.tools frontend.state tables
  simp only [encodeArtifact,encodeFrontend,List.length_append,List.length_singleton]
  rw [endpoints,calibration,PDLower.CalibrationCompute.encodeEndpointCache_length,PDLower.CalibrationCompute.encodeCalibrationCache_length]
  unfold outputBound PDLower.CalibrationCompute.rowWidth
  omega

theorem original_artifact_length_le (P : Parameters) (fee : ℚ) :
    (encodeArtifact (buildArtifact P fee)).length≤outputBound P.certificate.M P.certificate.stages P.tools:=by
  apply encodeArtifact_length_le_of_tables P (P.buildCachedFrontend fee) (selectorWeightRat P fee (P.buildCachedFrontend fee)) rfl rfl
  exact cached_search_tables_fit P fee (P.bisectionBudget fee)

/-- The output prefix property is supplied by the REAL ISA chain,
not inferred from the desired final list. Solver output is not summed. -/
theorem actual_output_prefix_bound (program : Program) (input : List Cell) (trace : List State) (final before : State)
    (chain : trace.IsChain (fun a b=>step program input a=some b)) (last : trace.getLast?=some final)
    (P : Parameters) (fee : ℚ) (output : final.output=before.output++encodeArtifact (buildArtifact P fee)) :
    ∀ state∈trace,state.output.length≤before.output.length+outputBound P.certificate.M P.certificate.stages P.tools:=by
  intro state member
  have outputLength:=(PDROC.D27Prepare.Output.chain_prefix_final program input trace final chain last state member).length_le
  rw [output,List.length_append] at outputLength
  exact outputLength.trans (Nat.add_le_add_left (original_artifact_length_le P fee) _)

end PDCompute.CoreMemory
