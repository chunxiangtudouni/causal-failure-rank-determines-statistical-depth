module

import Paid.RootD27Core_UniformPolynomial_096
public import RootD27Core_CanonicalCapsule_Claims_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace RootD27.Core.CanonicalCapsule

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits

attribute [local irreducible] PolynomialBound

/-- Two actual input-independent RAM programs and one common polynomial,
chosen before every original input. All resource bounds refer to the same
preparation/core executions that produce the exact original outputs. -/
public theorem actual_prepare_core_uniform :
    ∃ (prepare core : Program) (C degree : ℕ), 0 < C ∧
      ∀ (P : Parameters) (fee : ℚ), 0 ≤ fee →
        ∃ (prepareTrace : List State) (prepareFinal : State)
          (coreTrace : List State) (coreFinal : State),
          Runs prepare (rawInput P fee) prepareTrace prepareFinal ∧
          prepareFinal.output = preparedInput P fee ∧
          Runs core (preparedInput P fee) coreTrace coreFinal ∧
          decodeArtifact coreFinal.output = some (buildArtifact P fee) ∧
          coreFinal.output = encodeArtifact (buildArtifact P fee) ∧
          time prepare prepareTrace ≤ C * (variableGammaSize P fee)^degree ∧
          peakCells prepareTrace ≤ C * (variableGammaSize P fee)^degree ∧
          peakOperandBits prepareTrace ≤ C * (variableGammaSize P fee)^degree ∧
          time core coreTrace ≤ C * (variableGammaSize P fee)^degree ∧
          peakCells coreTrace ≤ C * (variableGammaSize P fee)^degree ∧
          peakOperandBits coreTrace ≤ C * (variableGammaSize P fee)^degree := by
  obtain ⟨prepare, _solver, _calibrate, core, _labels,
      Ctime, Cspace, Cbits, Cprepare, prepareDegree,
      _timePositive, _spacePositive, _bitsPositive, preparePositive, original⟩ :=
    uniform_rational_implementation_claims
  have positive := PDROC.D27Prepare.Resources.size_pos
  let c (n : ℕ) := PolynomialBound.constant PDROC.D27Prepare.Resources.size n
  have preparePolynomial : PolynomialBound PDROC.D27Prepare.Resources.size
      (fun x => Cprepare * (variableGammaSize x.1 x.2)^prepareDegree) := by
    unfold PolynomialBound
    exact ⟨Cprepare, prepareDegree, preparePositive, fun _ => Nat.le_refl _⟩
  have coreTimePolynomial := (c Ctime).mul sourceCoreScale_original_polynomial
  have coreSpacePolynomial := (c Cspace).mul sourceRecordSpace_original_polynomial
  have coreBitsPolynomial := (c Cbits).mul
    PDCompute.CoreGlobalBudget.coreOperandBound_original_polynomial
  have aggregate := ((preparePolynomial.add coreTimePolynomial positive).add
    coreSpacePolynomial positive).add coreBitsPolynomial positive
  unfold PolynomialBound at aggregate
  obtain ⟨C, degree, coefficientPositive, bounded⟩ := aggregate
  refine ⟨prepare, core, C, degree, coefficientPositive, ?_⟩
  intro P fee nonnegative
  obtain ⟨prepared, _solved, _calibrated, computed⟩ := original P fee nonnegative
  obtain ⟨prepareTrace, prepareFinal, prepareRun, prepareOutput, prepareTime, prepareSpace, prepareBits⟩ := prepared
  obtain ⟨coreTrace, coreFinal, coreRun, coreDecoded, coreOutput, coreTime, coreSpace, coreBits, _otherOriginalFields⟩ := computed
  have common : Cprepare * (variableGammaSize P fee)^prepareDegree +
      Ctime * sourceCoreScale P fee + Cspace * sourceRecordSpace P + Cbits * coreOperandBound P fee ≤
      C * (variableGammaSize P fee)^degree := bounded (P, fee)
  have prepareCap : Cprepare * (variableGammaSize P fee)^prepareDegree ≤
      C * (variableGammaSize P fee)^degree := by omega
  have coreTimeCap : Ctime * sourceCoreScale P fee ≤ C * (variableGammaSize P fee)^degree := by omega
  have coreSpaceCap : Cspace * sourceRecordSpace P ≤ C * (variableGammaSize P fee)^degree := by omega
  have coreBitsCap : Cbits * coreOperandBound P fee ≤ C * (variableGammaSize P fee)^degree := by omega
  exact ⟨prepareTrace, prepareFinal, coreTrace, coreFinal, prepareRun, prepareOutput,
    coreRun, coreDecoded, coreOutput, prepareTime.trans prepareCap, prepareSpace.trans prepareCap,
    prepareBits.trans prepareCap, coreTime.trans coreTimeCap, coreSpace.trans coreSpaceCap,
    coreBits.trans coreBitsCap⟩

end RootD27.Core.CanonicalCapsule
