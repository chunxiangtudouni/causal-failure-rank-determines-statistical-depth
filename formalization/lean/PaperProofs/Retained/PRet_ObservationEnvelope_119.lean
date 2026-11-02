module

public import PaperProofs.Retained.Controller

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetObservationEnvelope119

open Common Common.Native Statistics MeasureTheory
open scoped ENNReal

variable {I : Instance}

/-- The local observation price of the FIXED original retained SPRT at its
real rational target. This is neither a comparator value nor a Policy field. -/
noncomputable def localObservationPrice (input : StatisticalInput I) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (risk : ℚ) : ENNReal :=
  match referenceBudgetTarget kind risk with
  | none => 0
  | some target => (input.experiment stage).bayesObservationCharge (Measure.dirac ())
      ((input.experiment stage).posteriorSPRT target)

/-- A finite-tree numerical UPPER allowance for the fixed script, preserving
its original old-H rank cases, half-budget good child and actual bad-risk
clamp. The good branch is bounded by weight1; the bad child by its original
SPRT target. Infinite retained rank has zero future observation charge; real
terminal correction fees are handled separately by the native ledger bound. -/
noncomputable def observationEnvelopeAux (input : StatisticalInput I) :
    ℕ → ℕ → Finset I.Stage → ℚ → ENNReal
  | 0, _, _, _ => 0
  | fuel + 1, next, old, risk =>
    if h : next < I.stageCount then
      let stage : I.Stage := ⟨next, h⟩
      match rankCase I stage old with
      | none => 0
      | some .infiniteRank => 0
      | some .noTool => localObservationPrice input stage .noTool risk +
          observationEnvelopeAux input fuel (next + 1) old (risk / 2)
      | some (.finiteBad depth) =>
          let target := controllerTarget risk depth.val
          localObservationPrice input stage (.finiteBad depth) risk +
            observationEnvelopeAux input fuel (next + 1) old (risk / 2) +
            ENNReal.ofReal (target : ℝ) * observationEnvelopeAux input fuel (next + 1) (insert stage old)
              (controllerBadRisk risk target)
    else 0

noncomputable def observationEnvelope (input : StatisticalInput I) (next : ℕ)
    (old : Finset I.Stage) (risk : ℚ) : ENNReal :=
  observationEnvelopeAux input (I.stageCount - next) next old risk

/-- Pure numerical R05 allowance target. Its actual-run domination is a
separate obligation, never assumed as a performance certificate of a Policy.
The actual original idealPolicy starts its cache at budget/2. -/
def ObservationEnvelopeAsymptotics (input : StatisticalInput I) : Prop :=
  ∀ depth : ℕ, girth I = (depth : ℕ∞) → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ budget : ℚ,
      0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
        observationEnvelope input 0 ∅ (budget / 2) ≤
          ENNReal.ofReal ((1 + epsilon) * headCoefficient input * iteratedLog depth (budget : ℝ)⁻¹)

end PaperProofs.Retained.PRetObservationEnvelope119
