module

public import PaperProofs.Paid.PDMenu_EndpointNativeWeights_039
public import PaperProofs.Statistics.DecisionLaw

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Paid

def menuAnalysisHead : (freshInstance 1 0).Stage := ⟨0, by decide⟩

/-- The already-proved original endpoint test, presented in the exact
original paid experiment type for the subsequent analysis-only recursion. -/
noncomputable def menuAnalysisTest (P : Parameters) (level : ℕ) : P.experiment.AdmissibleRule Bool :=
  freshEndpointTest P 1 0 0 (by decide) menuAnalysisHead level

theorem menuAnalysisTest_conditionalError (P : Parameters) (level : ℕ) (truth : Bool) :
    P.experiment.conditionalError PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw
      (menuAnalysisTest P level) truth = ENNReal.ofReal (P.binarySymmetric.endpointError level : ℝ) :=
  PDROC.rocEndpointTest_conditionalError P.binarySymmetric level truth

theorem menuAnalysisTest_conditionalCharge (P : Parameters) (level : ℕ) (truth : Bool) :
    P.experiment.expectedObservationCharge PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw
      (menuAnalysisTest P level) truth = ENNReal.ofReal (P.binarySymmetric.endpointCharge level : ℝ) :=
  PDROC.rocEndpointTest_expectedCharge P.binarySymmetric level truth

theorem menuAnalysisTest_bayesError (P : Parameters) (level : ℕ) :
    P.experiment.bayesError PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw
      (menuAnalysisTest P level) = ENNReal.ofReal (P.binarySymmetric.endpointError level : ℝ) :=
  freshEndpointTest_bayesError P 1 0 0 (by decide) menuAnalysisHead level

theorem menuAnalysisTest_bayesCharge (P : Parameters) (level : ℕ) :
    P.experiment.bayesObservationCharge PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw
      (menuAnalysisTest P level) = ENNReal.ofReal (P.binarySymmetric.endpointCharge level : ℝ) :=
  freshEndpointTest_bayesCharge P 1 0 0 (by decide) menuAnalysisHead level

theorem menuAnalysisTest_expectedSamples_finite (P : Parameters) (level : ℕ) (truth : Bool) :
    P.experiment.expectedSamples PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw
      (menuAnalysisTest P level) truth ≠ ⊤ := by
  have hfinite : P.experiment.bayesObjective PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw
      (menuAnalysisTest P level) 0 ≠ ⊤ := by
    rw [PaperProofs.Statistics.BinaryExperiment.bayesObjective, zero_mul, add_zero, menuAnalysisTest_bayesCharge]
    exact ENNReal.ofReal_ne_top
  exact P.experiment.bayesObjective_finite_expectedSamples
    PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw (menuAnalysisTest P level) 0 hfinite truth

/-- Finiteness is a theorem of the fixed original endpoint, never an input
performance assumption on a native Policy or a summary. -/
theorem menuAnalysisTest_stop_ae_finite (P : Parameters) (level : ℕ) (truth : Bool) :
    ∀ᵐ sample ∂P.experiment.conditionalLaw PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw truth,
      (menuAnalysisTest P level).rule.stop sample.1 sample.2 ≠ ⊤ :=
  P.experiment.expectedSamples_finite_stop PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw
    (menuAnalysisTest P level) truth (menuAnalysisTest_expectedSamples_finite P level truth)

theorem menuAnalysisTest_zero_stop (P : Parameters) (seed : Bool) (tape : P.experiment.Tape) :
    (menuAnalysisTest P 0).rule.stop seed tape = 0 := rfl

theorem menuAnalysisTest_zero_decision (P : Parameters) (seed : Bool) (tape : P.experiment.Tape) :
    (menuAnalysisTest P 0).rule.decision seed tape = seed := rfl

end PDMenu
