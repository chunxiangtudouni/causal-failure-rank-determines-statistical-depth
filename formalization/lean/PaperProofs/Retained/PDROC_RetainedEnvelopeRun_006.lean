module

public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics
open PaperProofs.Retained.PRetObservationEnvelope119
open MeasureTheory
open scoped ENNReal

namespace PDROC.RetainedEnvelopeRun

variable {I : Instance}

theorem stageObservationBill_on_entry_le_localPrice (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (kind : ReferenceBudgetCase) (risk : ℚ)
    (target : PRetRiskMassFlow.entryTarget I budget stage history = referenceBudgetTarget kind risk) :
    (∫⁻ sample in stageEntryEvent input C accounting budget stage history,
      runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) ≤
      input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
        localObservationPrice input stage kind risk := by
  cases chosen : referenceBudgetTarget kind risk with
  | none =>
    rw [stageObservationBill_on_entry_none input C hretained accounting budget positive small stage history
      (target.trans chosen)]
    exact bot_le
  | some p =>
    simpa only [localObservationPrice, chosen] using
      stageObservationBill_on_entry_le input C hretained accounting budget positive small stage history p
        (target.trans chosen)

theorem errorMass_mul_badAllowance_le (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (kind : ReferenceBudgetCase)
    (cache : BudgetCache I)
    (target : PRetRiskMassFlow.entryTarget I budget stage history = referenceBudgetTarget kind cache.risk) :
    input.seededWorldLaw (Measure.dirac ())
      (PRetRiskMassFlow.writeError input C accounting budget stage ∩ stageEntryEvent input C accounting budget stage history) *
        Branch.badAllowance input stage cache.errors kind cache.risk ≤
      input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
        ((match referenceBudgetTarget kind cache.risk with
          | none => 0
          | some p => ENNReal.ofReal (p : ℝ)) * Branch.badAllowance input stage cache.errors kind cache.risk) := by
  cases chosen : referenceBudgetTarget kind cache.risk with
  | none =>
    have hbad : Branch.badAllowance input stage cache.errors kind cache.risk = 0 := by
      cases kind with
      | infiniteRank => rfl
      | noTool => rfl
      | finiteBad depth =>
        change some (controllerTarget cache.risk depth.val) = none at chosen
        cases chosen
    simp only [hbad, mul_zero, le_refl]
  | some p =>
    have mass := PRetRiskMassFlow.writeError_on_entry_le input C hretained accounting budget positive small
      stage history p (target.trans chosen)
    change input.seededWorldLaw (Measure.dirac ())
      (PRetRiskMassFlow.writeError input C accounting budget stage ∩ stageEntryEvent input C accounting budget stage history) ≤
      ENNReal.ofReal (p : ℝ) * input.seededWorldLaw (Measure.dirac ())
        (stageEntryEvent input C accounting budget stage history) at mass
    have weighted := mul_le_mul_right mass (Branch.badAllowance input stage cache.errors kind cache.risk)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using weighted

/-- Positive drift on every complete genuine entry-history atom. The
actual error mass is bounded before multiplying the exact original bad
child allowance. No finite-cost or continuation identity is assumed. -/
theorem stageEnvelope_drift_on_entry (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) :
    (∫⁻ sample in stageEntryEvent input C accounting budget stage history,
      runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) +
    (∫⁻ sample in stageEntryEvent input C accounting budget stage history,
      entryEnvelopePotential input C accounting budget (stage.val + 1) sample
      ∂input.seededWorldLaw (Measure.dirac ())) ≤
    (∫⁻ sample in stageEntryEvent input C accounting budget stage history,
      entryEnvelopePotential input C accounting budget stage.val sample
      ∂input.seededWorldLaw (Measure.dirac ())) := by
  classical
  by_cases nonempty : (stageEntryEvent input C accounting budget stage history).Nonempty
  · obtain ⟨sample, entered⟩ := nonempty
    obtain ⟨cache, kind, replay, healthy, _valid, query, _risk, _kind, target⟩ :=
      PRetRiskMassFlow.entry_cache input C hretained accounting budget positive small stage sample history entered
    have cost := stageObservationBill_on_entry_le_localPrice input C hretained accounting budget positive small
      stage history kind cache.risk target
    have future := lintegral_nextPotential_on_entry_le input C hretained accounting budget positive small
      stage history cache kind replay healthy query
    have bad := errorMass_mul_badAllowance_le input C hretained accounting budget positive small
      stage history kind cache target
    rw [lintegral_potential_on_entry input C accounting budget stage history cache replay]
    calc
      _ ≤ input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
          localObservationPrice input stage kind cache.risk +
          (input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
            Branch.goodAllowance input stage cache.errors kind cache.risk +
          input.seededWorldLaw (Measure.dirac ())
            (PRetRiskMassFlow.writeError input C accounting budget stage ∩ stageEntryEvent input C accounting budget stage history) *
            Branch.badAllowance input stage cache.errors kind cache.risk) := add_le_add cost future
      _ ≤ input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
          localObservationPrice input stage kind cache.risk +
          (input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
            Branch.goodAllowance input stage cache.errors kind cache.risk +
          input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
            ((match referenceBudgetTarget kind cache.risk with
              | none => 0
              | some p => ENNReal.ofReal (p : ℝ)) * Branch.badAllowance input stage cache.errors kind cache.risk)) :=
        add_le_add le_rfl (add_le_add le_rfl bad)
      _ = _ := by
        rw [Branch.currentEnvelope_decomposition input stage cache.errors kind cache.risk query]
        simp only [mul_add]
        ac_rfl
  · have empty : stageEntryEvent input C accounting budget stage history = ∅ := Set.not_nonempty_iff_eq_empty.mp nonempty
    simp only [empty, Measure.restrict_empty, lintegral_zero_measure, add_zero, le_refl]

end PDROC.RetainedEnvelopeRun
