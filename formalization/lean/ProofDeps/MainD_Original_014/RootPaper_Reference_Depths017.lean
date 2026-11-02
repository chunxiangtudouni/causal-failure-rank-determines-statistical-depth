module
public import RootPaper_Reference_ChargedBounds015
public import RootB236_RiskFold_TargetWidths010

/-! Every saved budget depth is produced by an actual original suffix DFS.
Its bound is numerical N+1, independent of F and of successful completion. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference RationalControllerComputation
variable {I : Instance}

theorem query_toNat_bound (I : Instance) (stage : Nat) (remaining : Finset I.Tool) :
    (query I stage remaining).rank.toNat≤I.stageCount := by
  obtain ⟨steps,final,_run,_cost,_atSteps,atFuel,_halted,answer,within,_carrier⟩:=
    RootB23.GenericRank.original_suffix_dfs I stage remaining
  have valid:=(within (3*generalStructureFactor I)).1
  rw [atFuel] at valid
  have control:=valid.2
  rw [answer] at control
  have bounded : RootB23.GenericRank.RankBound I.stageCount
      (PaperProofs.Structure.genericRank (I.compatibility.drop stage) remaining) :=
    RootB23.GenericRank.RankBound.mono control (RootB23.GenericRank.expected_le final.stack valid.1)
  rw [(query_spec I stage remaining).1]
  rcases bounded with infinite|finite
  · rw [infinite]
    exact Nat.zero_le _
  · exact ENat.toNat_le_of_le_natCast finite

theorem kindWork_depth (available : Finset I.Tool) (stage : I.Stage) (usedTools : Finset I.Tool)
    (kind : ReferenceBudgetCase) (actual : (kindWork I available stage usedTools).classification=some kind) :
    RootB236.RiskFold.caseDepth kind≤I.stageCount+1 := by
  cases kind with
  | infiniteRank => exact Nat.zero_le _
  | noTool => exact Nat.zero_le _
  | finiteBad depth =>
      dsimp only [kindWork] at actual
      cases picked : (query I stage.val (available\usedTools)).pick with
      | none =>
          rw [picked] at actual
          have ranks:=referenceCaseOfRanks_finite_spec _ _ depth actual
          have zero:=congrArg ENat.toNat ranks.2
          change 0=depth.val at zero
          have positive:=depth.pos
          omega
      | some tool =>
          rw [picked] at actual
          have ranks:=referenceCaseOfRanks_finite_spec _ _ depth actual
          have bounded:=query_toNat_bound I (stage.val+1) ((available\usedTools).erase tool)
          have same:=congrArg ENat.toNat ranks.2
          rw [ENat.toNat_natCast] at same
          change depth.val≤I.stageCount+1
          omega

theorem kernel_kind_depth (available : Finset I.Tool) (budget : Rat) (cache : ReferenceReplayCache I)
    (kind : ReferenceBudgetCase) (actual : (kernel I available budget cache).classification=some kind) :
    RootB236.RiskFold.caseDepth kind≤I.stageCount+1 := by
  unfold kernel at actual
  cases stage : referenceReplayStage I cache with
  | none => rw [stage] at actual;cases actual
  | some current =>
      rw [stage] at actual
      exact kindWork_depth available current (historyUsed cache.entryHistory) kind actual

theorem kernel_default_depth (available : Finset I.Tool) (budget : Rat) (cache : ReferenceReplayCache I) :
    RootB236.RiskFold.caseDepth ((kernel I available budget cache).classification.getD .infiniteRank)≤I.stageCount+1 := by
  cases classified : (kernel I available budget cache).classification with
  | none => exact Nat.zero_le _
  | some kind => exact kernel_kind_depth available budget cache kind classified

def EventDepths (I : Instance) (events : List ReferenceBudgetEvent) : Prop :=
  ∀ event∈events,RootB236.RiskFold.caseDepth event.1≤I.stageCount+1

private theorem selected_value (test : Prop) [Decidable test] (value next : ReferenceReplayCache I)
    (actual : (if test then some value else none)=some next) : value=next := by
  by_cases valid : test
  · rw [ite_eq_left valid] at actual
    exact Option.some.inj actual
  · rw [ite_eq_right valid] at actual
    cases actual

theorem bodyCalculation_events (input : StatisticalInput I) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (view : Snapshot I) (data : Kernel I)
    (recorded : ReferenceReplayCache I) (events : List ReferenceBudgetEvent) (reportCount : Nat)
    (next : ReferenceReplayCache I)
    (actual : (bodyCalculation input available cache event view data recorded events reportCount).1=some next) :
    next.events=recorded.events ∨ next.events=events := by
  unfold bodyCalculation at actual
  repeat' split at actual
  all_goals first
    | cases actual
    | (have same:=selected_value _ _ next actual;subst next)
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

theorem stepCalculation_depths (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (next : ReferenceReplayCache I)
    (depths : EventDepths I cache.events)
    (actual : (stepCalculation input available budget cache event).value=some next) : EventDepths I next.events := by
  dsimp only [stepCalculation] at actual
  rcases bodyCalculation_events input available cache event (snapshotCalculation cache).1
      (kernelCalculation available budget cache (snapshotCalculation cache).1).1
      {cache with seen:=(appendOne cache.seen event).1}
      (appendOne cache.events
        (((kernelCalculation available budget cache (snapshotCalculation cache).1).1.classification.getD .infiniteRank),
          reportError (snapshotCalculation cache).1 event)).1 (count cache.events).1 next actual with old|reported
  · rw [old]
    exact depths
  · intro item member
    rw [reported,(appendOne_spec _ _).1] at member
    rcases List.mem_append.mp member with before|last
    · exact depths item before
    · have same:=List.mem_singleton.mp last
      subst item
      dsimp only
      rw [kernelCalculation_value _ _ _ _ (snapshotCalculation_value cache)]
      exact kernel_default_depth available budget cache

theorem replayCalculation_depths (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (history : List (VisibleEvent I)) (next : ReferenceReplayCache I)
    (depths : EventDepths I cache.events)
    (actual : (replayCalculation input available budget cache history).value=some next) : EventDepths I next.events := by
  induction history generalizing cache with
  | nil =>
      have same : cache=next := Option.some.inj actual
      subst next
      exact depths
  | cons event rest ih =>
      dsimp only [replayCalculation] at actual
      cases front : (stepCalculation input available budget cache event).value with
      | none => rw [front] at actual;cases actual
      | some child =>
          rw [front] at actual
          exact ih child (stepCalculation_depths input available budget cache event child depths front) actual

theorem parseCalculation_depths (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I) (view : Snapshot I)
    (actual : (parseCalculation input available budget history).value=some (cache,view)) : EventDepths I cache.events := by
  have original :=parseCalculation_value input available budget history
  rw [actual] at original
  have parsed : referenceAvailableReplay input available budget history=some cache := original.symm
  have fold:=(referenceAvailableReplay_some_spec input available budget history cache parsed).2.1
  rw [←replayCalculation_value] at fold
  exact replayCalculation_depths input available budget (referenceReplayInitial I) history cache
    (by intro event impossible;cases impossible) fold

end RootPaper.Reference.Charged
