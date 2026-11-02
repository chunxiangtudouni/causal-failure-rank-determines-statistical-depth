module

public import PaperProofs.Retained.PRet_RiskMassFlow_Realization_005
public import PaperProofs.Common.ReferenceMassFlow

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetRiskMassFlow

variable {I : Instance}

def entryRisk (I : Instance) (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) : Option ℚ :=
  (replayBudget I budget history stage.val).map BudgetCache.risk

def entryKind (I : Instance) (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) : Option ReferenceBudgetCase :=
  (replayBudget I budget history stage.val).bind (fun cache => rankCase I stage cache.errors)

def entryEvent (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) : Set (Unit × input.World) :=
  {sample | entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some history}

def writeError (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) : Set (Unit × input.World) :=
  {sample | ∃ n, let state := run input C .uncapped accounting (retainedRule input budget none) sample n
    state.ledger.written stage = some (!state.ledger.truth stage)}

/-- A fatal branch is identified from the real entry's original old-H rank
and an actually written wrong bit; neither eventual success nor a tape event
is used to select the entry. -/
def fatal (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) : Set (Unit × input.World) :=
  writeError input C accounting budget stage ∩ {sample |
    (entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample).bind
      (entryKind I budget stage) = some .noTool}

noncomputable def entryBudgetPotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage) (sample : Unit × input.World) : ℝ≥0∞ :=
  match entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample with
  | none => 0
  | some history => ENNReal.ofReal ((entryRisk I budget stage history).getD 0 : ℝ)

theorem measurableSet_entryEvent (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) :
    MeasurableSet (entryEvent input C accounting budget stage history) :=
  (measurable_entryHistory input C .uncapped accounting (retainedRule input budget none)
    (measurable_of_countable _) stage) (measurableSet_singleton (some history))

theorem measurableSet_writeError (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) : MeasurableSet (writeError input C accounting budget stage) := by
  have eq : writeError input C accounting budget stage =
      ⋃ n : ℕ, {sample : Unit × input.World |
        let state := run input C .uncapped accounting (retainedRule input budget none) sample n
        state.ledger.written stage = some (!state.ledger.truth stage)} := by
    ext sample
    simp only [writeError,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [eq]
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_run input C .uncapped accounting (retainedRule input budget none) (measurable_of_countable _) n)
    (MeasurableSpace.measurableSet_top (s := {state : State I | state.ledger.written stage = some (!state.ledger.truth stage)}))

theorem measurableSet_fatal (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) : MeasurableSet (fatal input C accounting budget stage) :=
  (measurableSet_writeError input C accounting budget stage).inter
    ((MeasurableSpace.measurableSet_top (s := {entry : EntryHistory I | entry.bind (entryKind I budget stage) = some .noTool})).preimage
      (measurable_entryHistory input C .uncapped accounting (retainedRule input budget none) (measurable_of_countable _) stage))

theorem measurable_entryBudgetPotential (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) : Measurable (entryBudgetPotential input C accounting budget stage) := by
  exact (measurable_of_countable (fun entry : EntryHistory I => match entry with
    | none => (0 : ℝ≥0∞)
    | some history => ENNReal.ofReal ((entryRisk I budget stage history).getD 0 : ℝ))).comp
    (measurable_entryHistory input C .uncapped accounting (retainedRule input budget none) (measurable_of_countable _) stage)

theorem entry_cache (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (stage : I.Stage) (sample : Unit × input.World) (history : List (VisibleEvent I))
    (entered : sample ∈ entryEvent input C accounting budget stage history) :
    ∃ cache kind, replayBudget I budget history stage.val = some cache ∧ Healthy I stage.val cache.errors ∧
      ReferenceBudgetValid cache.risk ∧ rankCase I stage cache.errors = some kind ∧
      entryRisk I budget stage history = some cache.risk ∧ entryKind I budget stage history = some kind ∧
      entryTarget I budget stage history = referenceBudgetTarget kind cache.risk := by
  obtain ⟨n,cursor,_first,seen⟩ := (entryHistory_some_iff input C .uncapped accounting (retainedRule input budget none) stage sample history).mp entered
  obtain ⟨_,_,path⟩ := run_has_prefix input C .uncapped accounting (retainedRule input budget none)
    (retainedRule_uncapped_legal input C hretained accounting budget none) sample n
  obtain ⟨cache,replay⟩ := PRetAlignment.prefix_replay_exists input C hretained.1 accounting budget none sample.1 _ _ path
  rw [cursor,seen] at replay
  have initialValid : ReferenceBudgetValid (budget/2) := by constructor <;> linarith
  obtain ⟨healthy,valid,_errors⟩ := PRetAlignment.replayBudget_sound budget history initialValid stage.val
    (Nat.le_of_lt stage.isLt) cache replay
  obtain ⟨kind,query,_noTool⟩ := PRetAlignment.rankCase_exists stage cache.errors healthy
  refine ⟨cache,kind,replay,healthy,valid,query,?_,?_,?_⟩
  · simp only [entryRisk,replay,Option.map_some]
  · simp only [entryKind,replay,Option.bind_some,query]
  · rw [entryTarget_eq budget stage history cache replay,cacheTarget_eq stage cache valid,query]
    rfl

end PRetRiskMassFlow
