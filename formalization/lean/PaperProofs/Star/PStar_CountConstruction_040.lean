module

public import PaperProofs.Star.PStar_CountExpectedCost_034
public import PaperProofs.Star.PStar_CountTerminal_029
public import PaperProofs.Star.RootStarCostSum_001
public import PaperProofs.Star.RootStarEnvelope_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCountConstruction040

open Common Common.Native Parameters MeasureTheory PStarLR PStarActualHalt022 PStarCountProbability019
  PStarCountIdealRisk025 PStarCountTerminal029 PStarCountExpectedCost034 PStarCurrentImmediate007 PStarCurrentToolIdentity008
open scoped BigOperators ENNReal

theorem expectedCountObservationBound (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (countKind : kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst))
    (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1/4) :
    expectedObservationBill (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none (Seed := Unit)) (Measure.dirac ()) ≤
        ENNReal.ofReal (P.countObservationEnvelope P.tools r) := by
  have numerical : (∑ stage ∈ Finset.range (P.tools+1),
      prefixWeight P r stage * ENNReal.ofReal (P.channel.a * (Real.log (1 / stageTarget P r stage) + P.channel.h))) =
      ENNReal.ofReal (P.countObservationEnvelope P.tools r) := by
    simpa only [prefixWeight, stageTarget] using RootStarCostSum.count_cost_sum P r positive quarter
  exact (expectedCountObservationBill_le_weightedSum P order kind countKind C qualified accounting r positive quarter).trans_eq numerical

/-- Complete original C08 construction for BOTH ER orders and SF current,
retaining exact r, original actual scripts, runtime terminal criterion and
all-path fees. No performance/ET/H0/alignment premise is introduced. -/
theorem countControllerConstruction (P : PaperProofs.Star.Parameters) : P.CountControllerConstruction := by
  intro order kind countKind C qualified accounting r positive quarter
  have legal := reference_legal P order kind r C qualified accounting
  have referenceLegality : P.ReferenceLegality order kind r none C accounting :=
    ⟨{ rule := P.starReferenceRule order kind r none
       measurable_rule := P.measurable_starReferenceRule order kind r none
       legal := legal }, rfl⟩
  refine ⟨referenceLegality,
    countIdealRisk P order kind countKind C qualified accounting r positive quarter,
    expectedCountObservationBound P order kind countKind C qualified accounting r positive quarter,
    countTerminalCriterion P order kind countKind C qualified accounting r positive quarter,
    ?_, ?_, referenceAllPathCharges_of_legal P order kind r none C accounting legal⟩
  · intro retained
    subst kind
    exact retainedNoEarlyCommitment_of_legal P order .earlyRetained (by decide) r none C accounting legal
  · intro current
    subst kind
    exact ⟨immediateExecution P order r none C qualified.1 accounting,
      currentToolIdentities P order r none C accounting⟩

theorem c08Claims (P : PaperProofs.Star.Parameters) : P.C08Claims :=
  ⟨countControllerConstruction P, RootStarEnvelope.countEnvelopeAsymptotics P⟩

end PaperProofs.Star.PStarCountConstruction040
