module

public import PaperProofs.Common.NativeBellmanUpper
public import PaperProofs.Retained.PRet_RetainedGuard_007
public import PaperProofs.Retained.Controller

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshHeadPolicy079

open Common Common.Native MeasureTheory

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def rule (input : StatisticalInput I) (head : I.Stage)
    (test : (input.experiment head).AdmissibleRule Seed) (after : PolicyRule I Seed) : PolicyRule I Seed :=
  PRetRetainedGuard007.guarded (bellmanHeadThenRaw input head test after)

theorem measurable_rule (input : StatisticalInput I) (head : I.Stage)
    (test : (input.experiment head).AdmissibleRule Seed) (after : PolicyRule I Seed) (hm : MeasurableRule after) :
    MeasurableRule (rule input head test after) := by
  apply PRetRetainedGuard007.measurable_guarded
  apply measurable_from_prod_countable_left
  intro history
  dsimp only [bellmanHeadThenRaw]
  split_ifs
  · exact (measurable_bellmanHeadNext input head test).comp (measurable_id.prodMk measurable_const)
  · exact hm.comp (measurable_id.prodMk measurable_const)

/-- Actual uncapped full fresh Policy. Its guard is the repaired retained
public guard, so a lawful terminal continuation is not rejected because its
allocated stage lies behind the terminal cursor. -/
noncomputable def policy (input : StatisticalInput I) (head : I.Stage)
    (test : (input.experiment head).AdmissibleRule Seed) (after : PolicyRule I Seed) (hm : MeasurableRule after) :
    Policy input (freshContract I) .uncapped (zeroNormalAccounting I) Seed where
  rule := rule input head test after
  measurable_rule := measurable_rule input head test after hm
  legal := PRetRetainedGuard007.guarded_legal input (freshContract I) ⟨rfl, rfl, rfl⟩
    (zeroNormalAccounting I) (bellmanHeadThenRaw input head test after)

theorem rule_headReviewHistory (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (after : PolicyRule I Seed)
    (seed : Seed) (tape : (input.experiment head).Tape) (n : ℕ) :
    rule input head test after seed (headReviewHistory input head tape n) =
      bellmanHeadNext input head test seed (headReviewHistory input head tape n) := by
  have hc := historyCursor_headReviewHistory input head tape n
  have hw := historyWritten_headReviewHistory input head tape n
  simp only [rule, PRetRetainedGuard007.guarded, bellmanHeadThenRaw, hw, ite_true]
  apply ite_eq_left
  unfold bellmanHeadNext
  dsimp only
  split_ifs <;> exact ⟨hc.trans hhead.symm, hw⟩

end PaperProofs.Retained.PRetFreshHeadPolicy079
