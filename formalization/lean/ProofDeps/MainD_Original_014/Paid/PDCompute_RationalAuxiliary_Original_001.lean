module

public import Paid.PDROC_D27Prepare_Assembly_005
public import Paid.PDCompute_SolverUniformOriginal_214
public import Paid.PDLower_CalibrationCompute_StandaloneResources_129

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.RationalAuxiliary

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

/-- Precisely the FIRST THREE conjuncts of the original uniform rational
claim, with exactly its input quantifiers, encodings and resource scales.
The complete core field remains a separate Root-owned obligation. -/
def AuxiliaryFields (prepare solver calibrate : Program)
    (Ctime Cspace Cbits Cprepare degree : ℕ) : Prop :=
  ∀ (P : Parameters) (fee : ℚ), 0≤fee →
    (∃ trace final, Runs prepare (rawInput P fee) trace final ∧ final.output=preparedInput P fee ∧
      time prepare trace≤Cprepare*(variableGammaSize P fee)^degree ∧
      peakCells trace≤Cprepare*(variableGammaSize P fee)^degree ∧
      peakOperandBits trace≤Cprepare*(variableGammaSize P fee)^degree) ∧
    (∀ (penalty : ℚ) (n k : ℕ),∃ trace final,
      Runs solver (solveInput P fee penalty n k) trace final ∧
      final.output=encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n) ∧
      time solver trace≤Ctime*(n+1)*(k+1)*(P.certificate.M+1) ∧
      peakCells trace≤Cspace*(n+1)*(k+1) ∧
      peakOperandBits trace≤Cbits*((n+1)*(2*(P.certificate.M+1)+2)*(maximumMenuBits P fee+1)+
        ratEncodingBits penalty+natBits n+natBits k+1)) ∧
    (∃ trace final, Runs calibrate (calibrationInput P) trace final ∧
      final.output=encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList ∧
      time calibrate trace≤Ctime*P.certificate.Q*(P.certificate.M+1)^2 ∧
      peakCells trace≤Cspace*(P.certificate.M+1) ∧
      peakOperandBits trace≤Cbits*((P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)+
        maximumMenuBits P fee+1))

/-- All fixed programs and all common positive constants precede EVERY
input. Each original field retains its own ONE actual initial-to-HALT
witness with simultaneous output/time/space/full-operand-bit bounds. -/
theorem original_auxiliary_fields :
    ∃ (prepare solver calibrate : Program) (Ctime Cspace Cbits Cprepare degree : ℕ),
      0<Ctime ∧ 0<Cspace ∧ 0<Cbits ∧ 0<Cprepare ∧
      AuxiliaryFields prepare solver calibrate Ctime Cspace Cbits Cprepare degree := by
  obtain ⟨prepare,Cprepare,degree,preparePositive,prepareField⟩:=
    PDROC.D27Prepare.Assembly.exact_prepare_claims
  obtain ⟨solver,solverTime,solverSpace,solverBits,solverTimePositive,solverSpacePositive,solverBitsPositive,solverField⟩:=
    PDCompute.Solver.solver_uniform_original
  obtain ⟨calibrate,calibrationTime,calibrationSpace,calibrationBits,
    _calibrationTimePositive,_calibrationSpacePositive,_calibrationBitsPositive,calibrationField⟩:=
    PDLower.CalibrationCompute.original_calibration_resources
  refine ⟨prepare,solver,calibrate,solverTime+calibrationTime,solverSpace+calibrationSpace,
    solverBits+calibrationBits,Cprepare,degree,by omega,by omega,by omega,preparePositive,?_⟩
  intro P fee nonnegative
  refine ⟨prepareField P fee nonnegative,?_,?_⟩
  · intro penalty n k
    obtain ⟨trace,final,run,output,cost,space,bits⟩:=solverField P fee penalty n k
    refine ⟨trace,final,run,output,cost.trans ?_,space.trans ?_,bits.trans ?_⟩
    · exact Nat.mul_le_mul_right (P.certificate.M+1)
        (Nat.mul_le_mul_right (k+1) (Nat.mul_le_mul_right (n+1) (Nat.le_add_right _ _)))
    · exact Nat.mul_le_mul_right (k+1) (Nat.mul_le_mul_right (n+1) (Nat.le_add_right _ _))
    · exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · obtain ⟨trace,final,run,output,cost,space,bits⟩:=calibrationField P fee
    refine ⟨trace,final,run,output,cost.trans ?_,space.trans ?_,bits.trans ?_⟩
    · exact Nat.mul_le_mul_right ((P.certificate.M+1)^2)
        (Nat.mul_le_mul_right P.certificate.Q (Nat.le_add_left _ _))
    · exact Nat.mul_le_mul_right (P.certificate.M+1) (Nat.le_add_left _ _)
    · exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- Raising the common constants retains the SAME programs and witnesses.
This lets Root share its larger complete-core constants without any
recompilation or change of the original auxiliary resource statements. -/
theorem AuxiliaryFields.mono {prepare solver calibrate : Program}
    {Ctime Cspace Cbits Cprepare degree Dtime Dspace Dbits Dprepare : ℕ}
    (fields : AuxiliaryFields prepare solver calibrate Ctime Cspace Cbits Cprepare degree)
    (timeBound : Ctime≤Dtime) (spaceBound : Cspace≤Dspace)
    (bitBound : Cbits≤Dbits) (prepareBound : Cprepare≤Dprepare) :
    AuxiliaryFields prepare solver calibrate Dtime Dspace Dbits Dprepare degree := by
  intro P fee nonnegative
  obtain ⟨prepareField,solverField,calibrationField⟩:=fields P fee nonnegative
  refine ⟨?_,?_,?_⟩
  · obtain ⟨trace,final,run,output,cost,space,bits⟩:=prepareField
    have bound:=Nat.mul_le_mul_right ((variableGammaSize P fee)^degree) prepareBound
    exact ⟨trace,final,run,output,cost.trans bound,space.trans bound,bits.trans bound⟩
  · intro penalty n k
    obtain ⟨trace,final,run,output,cost,space,bits⟩:=solverField penalty n k
    refine ⟨trace,final,run,output,cost.trans ?_,space.trans ?_,bits.trans ?_⟩
    · exact Nat.mul_le_mul_right (P.certificate.M+1)
        (Nat.mul_le_mul_right (k+1) (Nat.mul_le_mul_right (n+1) timeBound))
    · exact Nat.mul_le_mul_right (k+1) (Nat.mul_le_mul_right (n+1) spaceBound)
    · exact Nat.mul_le_mul_right _ bitBound
  · obtain ⟨trace,final,run,output,cost,space,bits⟩:=calibrationField
    refine ⟨trace,final,run,output,cost.trans ?_,space.trans ?_,bits.trans ?_⟩
    · exact Nat.mul_le_mul_right ((P.certificate.M+1)^2) (Nat.mul_le_mul_right P.certificate.Q timeBound)
    · exact Nat.mul_le_mul_right (P.certificate.M+1) spaceBound
    · exact Nat.mul_le_mul_right _ bitBound

/-- Exact assembly into the original proposition. The premise below is
the ENTIRE original core field, including all genuine entry counts,
exact source request log, original serialization and fixed return windows.
This theorem supplies no proof of that remaining core premise. -/
theorem uniform_of_auxiliary_and_core
    (prepare solver calibrate core : Program) (labels : RoutineLabels)
    (Ctime Cspace Cbits Cprepare degree : ℕ)
    (positiveTime : 0<Ctime) (positiveSpace : 0<Cspace)
    (positiveBits : 0<Cbits) (positivePrepare : 0<Cprepare)
    (auxiliary : AuxiliaryFields prepare solver calibrate Ctime Cspace Cbits Cprepare degree)
    (completeCore : ∀ (P : Parameters) (fee : ℚ), 0≤fee →
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
        SolverCallRefinement core labels P fee Ctime trace) :
    UniformRationalImplementationClaims := by
  refine ⟨prepare,solver,calibrate,core,labels,Ctime,Cspace,Cbits,Cprepare,degree,
    positiveTime,positiveSpace,positiveBits,positivePrepare,?_⟩
  intro P fee nonnegative
  obtain ⟨prepareField,solverField,calibrationField⟩:=auxiliary P fee nonnegative
  exact ⟨prepareField,solverField,calibrationField,completeCore P fee nonnegative⟩

end PDCompute.RationalAuxiliary
