module

public import PaperProofs.Retained.PRet_RiskMassFlow_FailureCover_017
public import PaperProofs.Retained.PDROC_RetainedReturn_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetInfiniteRisk

variable {I : Instance}

theorem rankIndex_none_of_girth_top (hg : girth I = ⊤) (next : ℕ) (old : Finset I.Stage) :
    rankIndex I next old = none := by
  classical
  apply List.find?_eq_none.mpr
  intro depth _ selected
  have bad : ∃ future ∈ (stagesFrom I next).toFinset.powerset,
      future.card ≤ depth ∧ ¬Matchable I (old ∪ future) := of_decide_eq_true selected
  obtain ⟨future,_member,_card,obstructed⟩ := bad
  exact obstructed (((girth_eq_top_iff_matchable_univ I).mp hg).subset (Finset.subset_univ _))

theorem rankCase_infinite_of_girth_top (hg : girth I = ⊤) (stage : I.Stage) (old : Finset I.Stage) :
    rankCase I stage old = some .infiniteRank := by
  simp only [rankCase,rankIndex_none_of_girth_top hg]

theorem fatal_eq_empty_of_girth_top (input : StatisticalInput I) (hg : girth I = ⊤)
    (C : Contract I) (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage) :
    PRetRiskMassFlow.fatal input C accounting budget stage = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro sample member
  have selected : (entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample).bind
      (PRetRiskMassFlow.entryKind I budget stage) = some .noTool := member.2
  cases entered : entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample with
  | none => rw [entered] at selected; cases selected
  | some history =>
    rw [entered] at selected
    change PRetRiskMassFlow.entryKind I budget stage history = some .noTool at selected
    unfold PRetRiskMassFlow.entryKind at selected
    cases replay : replayBudget I budget history stage.val with
    | none => rw [replay] at selected; cases selected
    | some cache =>
      rw [replay] at selected
      change rankCase I stage cache.errors = some .noTool at selected
      rw [rankCase_infinite_of_girth_top hg] at selected
      cases selected

theorem idealRisk_zero_of_girth_top (input : StatisticalInput I) (hg : girth I = ⊤)
    (C : Contract I) (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2) :
    risk input C .uncapped accounting (idealPolicy input C hretained accounting budget).rule (Measure.dirac ()) = 0 := by
  have nontermination : input.seededWorldLaw (Measure.dirac ()) {sample : Unit × input.World |
      ¬∃ n,(run input C .uncapped accounting (retainedRule input budget none) sample n).halted = true} = 0 := by
    exact PDROC.RetainedReturn.idealPolicy_nontermination_measure_zero
      input C hretained accounting budget positive small
  have noFatal : (⋃ stage : I.Stage,PRetRiskMassFlow.fatal input C accounting budget stage) = ∅ := by
    simp only [fatal_eq_empty_of_girth_top input hg,Set.iUnion_empty]
  apply le_antisymm ?_ zero_le
  calc
    _ ≤ input.seededWorldLaw (Measure.dirac ())
        ({sample : Unit × input.World | ¬∃ n,(run input C .uncapped accounting (retainedRule input budget none) sample n).halted = true} ∪
          ⋃ stage : I.Stage,PRetRiskMassFlow.fatal input C accounting budget stage) :=
      measure_mono (PRetRiskMassFlow.failure_subset_nontermination_union_fatal
        input C hretained accounting budget positive small)
    _ ≤ input.seededWorldLaw (Measure.dirac ()) {sample : Unit × input.World |
        ¬∃ n,(run input C .uncapped accounting (retainedRule input budget none) sample n).halted = true} +
        input.seededWorldLaw (Measure.dirac ()) (⋃ stage : I.Stage,PRetRiskMassFlow.fatal input C accounting budget stage) :=
      measure_union_le _ _
    _ = 0 := by rw [nontermination,noFatal,measure_empty,add_zero]

end PRetInfiniteRisk
