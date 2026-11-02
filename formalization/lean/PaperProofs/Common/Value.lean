module

public import PaperProofs.Common.Model
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
Extended nonnegative cost and the constrained-infimum interface.
No probability law or admissible-policy predicate is postulated by this module.
The native interpretation must still be supplied and verified separately.
-/

@[expose] public section

namespace PaperProofs.Common

open MeasureTheory
open scoped ENNReal

noncomputable def expectedActualBill {I : Instance} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (run : Ω → Ledger I) (F : Fees I) : ℝ≥0∞ :=
  ∫⁻ ω, (run ω).actualBill F ∂μ

noncomputable def failureRisk {I : Instance} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (run : Ω → Ledger I) (C : Contract I) : ℝ≥0∞ :=
  μ {ω | (run ω).failure C}

/-- Empty feasible classes have value infinity, not the real-number convention zero. -/
noncomputable def constrainedValue {P : Type*} (legal : P → Prop)
    (risk cost : P → ℝ≥0∞) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ p : {p // legal p ∧ risk p ≤ δ}, cost p.val

theorem constrainedValue_le {P : Type*} {legal : P → Prop}
    {risk cost : P → ℝ≥0∞} {δ : ℝ≥0∞} (p : P)
    (hl : legal p) (hr : risk p ≤ δ) :
    constrainedValue legal risk cost δ ≤ cost p :=
  iInf_le (fun q : {p // legal p ∧ risk p ≤ δ} ↦ cost q.val) ⟨p, hl, hr⟩

/-- Enlarging the legal comparator can only lower its value. -/
theorem constrainedValue_of_comparator_inclusion {P : Type*}
    {small large : P → Prop} {risk cost : P → ℝ≥0∞} {δ : ℝ≥0∞}
    (h : ∀ p, small p → large p) :
    constrainedValue large risk cost δ ≤ constrainedValue small risk cost δ := by
  refine le_iInf fun p ↦ ?_
  exact constrainedValue_le p.val (h p.val p.property.1) p.property.2

theorem expectedObservationBill_le_expectedActualBill {I : Instance} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (run : Ω → Ledger I) (F : Fees I) :
    (∫⁻ ω, (run ω).observationBill F ∂μ) ≤ expectedActualBill μ run F := by
  exact lintegral_mono fun ω ↦ (run ω).observationBill_le_actualBill F

end PaperProofs.Common
