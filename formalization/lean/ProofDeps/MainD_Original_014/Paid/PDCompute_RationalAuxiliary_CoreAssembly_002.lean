module

public import Paid.PDCompute_RationalAuxiliary_Original_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.RationalAuxiliary

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

/-- Exactly the remaining FOURTH original field. This definition does
not prove it; Root must supply the actual complete core and labels. -/
def CoreField (core : Program) (labels : RoutineLabels) (Ctime Cspace Cbits : ℕ) : Prop :=
  ∀ (P : Parameters) (fee : ℚ), 0≤fee →
    ∃ trace final, Runs core (preparedInput P fee) trace final ∧
      decodeArtifact final.output=some (buildArtifact P fee) ∧
      final.output=encodeArtifact (buildArtifact P fee) ∧
      time core trace≤Ctime*sourceCoreScale P fee ∧
      peakCells trace≤Cspace*sourceRecordSpace P ∧
      peakOperandBits trace≤Cbits*coreOperandBound P fee ∧
      actualSolveRequests labels trace=(P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2 ∧
      entryCount labels.solveEntry trace=(actualSolveRequests labels trace).length ∧
      entryCount labels.solveEntry trace≤P.bisectionBudget fee+2 ∧
      entryCount labels.endpointEntry trace=1 ∧ entryCount labels.calibrationEntry trace=1 ∧
      SolverCallRefinement core labels P fee Ctime trace

/-- Raise only the window constant in the ORIGINAL indexed call predicate;
the fixed global return marker, exact table and actual trace are retained. -/
theorem original_call_constant_mono {program : Program} {labels : RoutineLabels}
    {P : Parameters} {fee : ℚ} {states : List State} {first later : ℕ}
    (calls : SolverCallRefinement program labels P fee first states) (bound : first≤later) :
    SolverCallRefinement program labels P fee later states := by
  intro index state found position
  obtain ⟨penalty,total,returned,final,base,strict,atReturn,marker,address,live,table,cost⟩:=
    calls index state found position
  refine ⟨penalty,total,returned,final,base,strict,atReturn,marker,address,live,table,cost.trans ?_⟩
  exact Nat.mul_le_mul_right (P.certificate.M+1)
    (Nat.mul_le_mul_right (P.tools+1) (Nat.mul_le_mul_right (P.certificate.stages+1) bound))

/-- The complete original core field is monotone in the same shared
constants, including its actual indexed solver execution windows. -/
theorem CoreField.mono {core : Program} {labels : RoutineLabels}
    {Ctime Cspace Cbits Dtime Dspace Dbits : ℕ}
    (field : CoreField core labels Ctime Cspace Cbits)
    (timeBound : Ctime≤Dtime) (spaceBound : Cspace≤Dspace) (bitBound : Cbits≤Dbits) :
    CoreField core labels Dtime Dspace Dbits := by
  intro P fee nonnegative
  obtain ⟨trace,final,run,decoded,encoded,cost,space,bits,requests,count,countBound,endpoints,calibration,calls⟩:=
    field P fee nonnegative
  exact ⟨trace,final,run,decoded,encoded,cost.trans (Nat.mul_le_mul_right _ timeBound),
    space.trans (Nat.mul_le_mul_right _ spaceBound),bits.trans (Nat.mul_le_mul_right _ bitBound),
    requests,count,countBound,endpoints,calibration,original_call_constant_mono calls timeBound⟩

/-- Root need supply ONLY its complete exact original core field, with
its own input-independent constants. The three proven auxiliary fields
and the entire core field automatically share larger positive constants.
No proof of CoreField is asserted here, and no D27 acceptance is claimed. -/
theorem original_uniform_of_core (core : Program) (labels : RoutineLabels)
    (coreTime coreSpace coreBits : ℕ) (complete : CoreField core labels coreTime coreSpace coreBits) :
    UniformRationalImplementationClaims := by
  obtain ⟨prepare,solver,calibrate,Ctime,Cspace,Cbits,Cprepare,degree,
    timePositive,spacePositive,bitsPositive,preparePositive,auxiliary⟩:=original_auxiliary_fields
  have commonAuxiliary:=auxiliary.mono (Nat.le_add_right Ctime coreTime) (Nat.le_add_right Cspace coreSpace)
    (Nat.le_add_right Cbits coreBits) (Nat.le_refl Cprepare)
  have commonCore:=complete.mono (Nat.le_add_left coreTime Ctime) (Nat.le_add_left coreSpace Cspace)
    (Nat.le_add_left coreBits Cbits)
  exact uniform_of_auxiliary_and_core prepare solver calibrate core labels
    (Ctime+coreTime) (Cspace+coreSpace) (Cbits+coreBits) Cprepare degree
    (by omega) (by omega) (by omega) preparePositive commonAuxiliary commonCore

end PDCompute.RationalAuxiliary
