module

public import PaperProofs.Retained.PRet_RiskMassFlow_Transition_010
public import PaperProofs.Retained.PRet_RiskMassFlow_EntryIntegral_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetRiskMassFlow

variable {I : Instance}

noncomputable def childBudgetEnvelope (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (risk : ℚ) (sample : Unit × input.World) : ℝ≥0∞ := by
  classical
  exact match kind with
  | .infiniteRank => ENNReal.ofReal (risk : ℝ)
  | .noTool => ENNReal.ofReal ((risk/2 : ℚ) : ℝ)
  | .finiteBad depth => ENNReal.ofReal ((risk/2 : ℚ) : ℝ) +
      (writeError input C accounting budget stage).indicator
        (fun _ => ENNReal.ofReal ((controllerBadRisk risk (controllerTarget risk depth.val) : ℚ) : ℝ)) sample

theorem nextEntryBudget_le_on_entry (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (stage nextStage : I.Stage) (successor : nextStage.val = stage.val+1)
    (history : List (VisibleEvent I)) (kind : ReferenceBudgetCase) (risk : ℚ)
    (kindEq : entryKind I budget stage history = some kind) (riskEq : entryRisk I budget stage history = some risk)
    (sample : Unit × input.World) (entered : sample ∈ entryEvent input C accounting budget stage history) :
    entryBudgetPotential input C accounting budget nextStage sample ≤
      childBudgetEnvelope input C accounting budget stage kind risk sample := by
  classical
  cases nextEntered : entryHistory input C .uncapped accounting (retainedRule input budget none) nextStage sample with
  | none => simp only [entryBudgetPotential,nextEntered]; exact zero_le
  | some nextHistory =>
    obtain ⟨cache,child,actualKind,error,replay,nextReplay,_healthy,_valid,_childHealthy,_childValid,query,update,_errors,wrong⟩ :=
      nextEntry_cache_transition input C hretained accounting budget positive small stage nextStage successor sample
        history nextHistory entered nextEntered
    have actualKindEq : entryKind I budget stage history = some actualKind := by
      simp only [entryKind,replay,Option.bind_some,query]
    have actualRiskEq : entryRisk I budget stage history = some cache.risk := by
      simp only [entryRisk,replay,Option.map_some]
    have sameKind : actualKind = kind := Option.some.inj (actualKindEq.symm.trans kindEq)
    subst actualKind
    have sameRisk : cache.risk = risk := Option.some.inj (actualRiskEq.symm.trans riskEq)
    rw [sameRisk] at update
    simp only [entryBudgetPotential,nextEntered,entryRisk,nextReplay,Option.map_some,Option.getD_some]
    cases kind with
    | infiniteRank =>
      have childEq : child.risk = risk := (Option.some.inj update).symm
      rw [childEq]
      exact le_rfl
    | noTool =>
      cases error with
      | false =>
        have childEq : child.risk = risk/2 := (Option.some.inj update).symm
        rw [childEq]
        exact le_rfl
      | true => cases update
    | finiteBad depth =>
      cases error with
      | false =>
        have childEq : child.risk = risk/2 := (Option.some.inj update).symm
        rw [childEq]
        exact le_add_of_nonneg_right zero_le
      | true =>
        have childEq : child.risk = controllerBadRisk risk (controllerTarget risk depth.val) := (Option.some.inj update).symm
        rw [childEq]
        simp only [childBudgetEnvelope,Set.indicator_of_mem (wrong rfl)]
        exact le_add_of_nonneg_left zero_le

noncomputable def nextBudgetPotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage) (sample : Unit × input.World) : ℝ≥0∞ :=
  if h : stage.val+1 < I.stageCount then entryBudgetPotential input C accounting budget ⟨stage.val+1,h⟩ sample else 0

theorem measurable_nextBudgetPotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage) :
    Measurable (nextBudgetPotential input C accounting budget stage) := by
  unfold nextBudgetPotential
  split_ifs with bound
  · exact measurable_entryBudgetPotential input C accounting budget ⟨stage.val+1,bound⟩
  · exact measurable_const

theorem nextBudget_zero_of_no_entry (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (stage : I.Stage) (sample : Unit × input.World)
    (absent : entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = none) :
    nextBudgetPotential input C accounting budget stage sample = 0 := by
  unfold nextBudgetPotential
  split_ifs with bound
  · cases nextEntered : entryHistory input C .uncapped accounting (retainedRule input budget none) ⟨stage.val+1,bound⟩ sample with
    | none => simp only [entryBudgetPotential,nextEntered]
    | some history =>
      obtain ⟨n,state,next,path,_runEq,advance,_selected,_seen⟩ :=
        nextEntry_has_advance input C hretained accounting budget sample stage ⟨stage.val+1,bound⟩ rfl history nextEntered
      have active := step_source_active input C .uncapped accounting (worldTapes input sample.2) advance
      have cursor : state.cursor = stage.val := by cases advance with | advance _ live _ _ => exact live.2
      obtain ⟨oldHistory,entered,_replay,_progress⟩ :=
        prefix_testing_origin input C hretained accounting budget positive small sample path active stage cursor
      rw [absent] at entered
      cases entered
  · rfl

end PRetRiskMassFlow
