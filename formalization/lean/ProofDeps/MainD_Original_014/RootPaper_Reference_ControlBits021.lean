module
public import RootPaper_Reference_Fees020
public import RootPaper_TableCost_Ports013

/-! Original data bounds at every actually visited replay cache, including
the cache at which an event is rejected. Natural guards and counters are
priced by closed binary primitives in Fees020, not as free Nat operations. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference RationalControllerComputation PSTRWordBool
variable {I : Instance}

def CacheSubset (whole : List (VisibleEvent I)) (cache : ReferenceReplayCache I) : Prop :=
  cache.seen⊆whole ∧ cache.entryHistory⊆whole

private theorem selected_cache (test : Prop) [Decidable test] (value next : ReferenceReplayCache I)
    (actual : (if test then some value else none)=some next) : value=next := by
  by_cases valid : test
  · rw [ite_eq_left valid] at actual
    exact Option.some.inj actual
  · rw [ite_eq_right valid] at actual
    cases actual

theorem bodyCalculation_data (input : StatisticalInput I) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (view : Snapshot I) (data : Kernel I)
    (recorded : ReferenceReplayCache I) (events : List ReferenceBudgetEvent) (reportCount : Nat)
    (next : ReferenceReplayCache I)
    (actual : (bodyCalculation input available cache event view data recorded events reportCount).1=some next) :
    next.seen=recorded.seen ∧ (next.entryHistory=recorded.entryHistory ∨ next.entryHistory=recorded.seen) := by
  unfold bodyCalculation at actual
  repeat' split at actual
  all_goals first | cases actual | (have same:=selected_cache _ _ next actual;subst next)
  all_goals first | exact ⟨rfl,Or.inl rfl⟩ | exact ⟨rfl,Or.inr rfl⟩

theorem stepCalculation_subset (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (next : ReferenceReplayCache I)
    (whole : List (VisibleEvent I)) (old : CacheSubset whole cache) (present : event∈whole)
    (actual : (stepCalculation input available budget cache event).value=some next) : CacheSubset whole next := by
  have extended : (appendOne cache.seen event).1⊆whole := by
    rw [(appendOne_spec _ _).1]
    intro item member
    rcases List.mem_append.mp member with before|last
    · exact old.1 before
    · exact List.mem_singleton.mp last ▸ present
  dsimp only [stepCalculation] at actual
  obtain ⟨seen,entry⟩:=bodyCalculation_data input available cache event (snapshotCalculation cache).1
    (kernelCalculation available budget cache (snapshotCalculation cache).1).1
    {cache with seen:=(appendOne cache.seen event).1}
    (appendOne cache.events
      (((kernelCalculation available budget cache (snapshotCalculation cache).1).1.classification.getD .infiniteRank),
        reportError (snapshotCalculation cache).1 event)).1 (count cache.events).1 next actual
  refine ⟨?_,?_⟩
  · rw [seen];exact extended
  · rcases entry with before|new
    · rw [before];exact old.2
    · rw [new];exact extended

/-- Erased list of the caches at which the SAME replay evaluates a step.
The final cache is included; no additional runtime replay is performed. -/
def visitedCaches (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) : List (VisibleEvent I)→List (ReferenceReplayCache I)
  | [] => [cache]
  | event::rest => cache::match (stepCalculation input available budget cache event).value with
      | none => []
      | some next => visitedCaches input available budget next rest

theorem cacheBound_widen {small large : Nat} (cache : ReferenceReplayCache I)
    (ordered : small≤large) (bounded : CacheBound small cache) : CacheBound large cache :=
  ⟨bounded.1.trans ordered,bounded.2.1.trans ordered,bounded.2.2.trans ordered⟩

theorem visitedCaches_data (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (whole history : List (VisibleEvent I)) (limit : Nat)
    (bounded : CacheBound limit cache) (subset : CacheSubset whole cache) (depths : EventDepths I cache.events)
    (remaining : history⊆whole) :
    ∀ before∈visitedCaches input available budget cache history,
      CacheBound (limit+history.length) before ∧ CacheSubset whole before ∧ EventDepths I before.events := by
  induction history generalizing cache limit with
  | nil =>
      intro before member
      cases List.mem_singleton.mp member
      exact ⟨bounded,subset,depths⟩
  | cons event rest ih =>
      intro before member
      simp only [visitedCaches,List.mem_cons] at member
      rcases member with rfl|later
      · exact ⟨cacheBound_widen _ (Nat.le_add_right _ _) bounded,subset,depths⟩
      · cases selected : (stepCalculation input available budget cache event).value with
        | none => rw [selected] at later;cases later
        | some child =>
            rw [selected] at later
            have childBound:=step_cacheBound input available budget cache child event limit bounded
              ((stepCalculation_value input available budget cache event).symm.trans selected)
            have childSubset:=stepCalculation_subset input available budget cache event child whole subset
              (remaining List.mem_cons_self) selected
            have childDepth:=stepCalculation_depths input available budget cache event child depths selected
            have result:=ih child (limit+1) childBound childSubset childDepth
              (fun item inside => remaining (List.mem_cons_of_mem _ inside)) before later
            have same : limit+1+rest.length=limit+(event::rest).length := by simp only [List.length_cons];omega
            rw [same] at result
            exact result

theorem initial_visited_data (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (history : List (VisibleEvent I)) :
    ∀ before∈visitedCaches input available budget (referenceReplayInitial I) history,
      CacheBound history.length before ∧ CacheSubset history before ∧ EventDepths I before.events := by
  simpa only [Nat.zero_add] using visitedCaches_data input available budget (referenceReplayInitial I)
    history history 0 initial_cacheBound (by constructor <;> intro event impossible <;> cases impossible)
    (by intro event impossible;cases impossible) (fun _ member=>member)

theorem reported_serial_bits (history : List (VisibleEvent I)) (stage : I.Stage) (B : Nat)
    (fields : RootPaper.TableCost.HistoryFieldBits B history) :
    natBits (((historyReport history stage).map Prod.snd).getD 0)≤B+1 := by
  cases found : historyReport history stage with
  | none => change 1≤B+1;omega
  | some reported =>
      have present : reported∈history.filterMap (eventReport stage) := List.mem_of_getLast? found
      obtain ⟨event,inside,selected⟩:=List.mem_filterMap.mp present
      cases event with
      | report other truth serial =>
          simp only [eventReport] at selected
          split_ifs at selected
          · have same:=congrArg Prod.snd (Option.some.inj selected)
            have bounded:=fields (.report other truth serial) inside serial (by simp [encodeEvent])
            simp only [Option.map_some,Option.getD_some,←same]
            omega
      | observation | wrote | committed | executed | advanced | stopped | abandoned => cases selected

structure SnapshotFields (B : Nat) (view : Snapshot I) : Prop where
  cursor : view.cursor≤B
  actions : view.actions≤B
  written : natBits ((view.written.map Prod.snd).getD 0)≤B+1
  reported : natBits ((view.reported.map Prod.snd).getD 0)≤B+1
  symbols : ∀ symbol∈view.observations,natBits symbol≤B
  observations : view.observations.length≤B

theorem snapshot_fields (cache : ReferenceReplayCache I) (B : Nat) (counted : cache.seen.length≤B)
    (fields : RootPaper.TableCost.HistoryFieldBits B cache.seen) :
    SnapshotFields B (RootPaper.Reference.snapshot cache) := by
  have cursor : historyCursor cache.seen≤B := (List.length_filterMap_le _ _).trans counted
  have actions : (historyActions cache.seen).length≤B := (List.length_filterMap_le _ _).trans counted
  cases current : referenceReplayStage I cache with
  | none =>
      rw [snapshot_none cache current]
      refine ⟨cursor,actions,?_,?_,?_,Nat.zero_le _⟩
      · change 1≤B+1;omega
      · change 1≤B+1;omega
      · intro symbol impossible;cases impossible
  | some stage =>
      rw [snapshot_some cache stage current]
      exact ⟨cursor,actions,RootPaper.TableCost.written_serial_bits cache.seen stage B fields,
        reported_serial_bits cache.seen stage B fields,
        RootPaper.TableCost.observation_bits cache.seen stage B fields,
        (List.length_filterMap_le _ _).trans counted⟩

theorem visited_snapshot_fields (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (history : List (VisibleEvent I)) (B : Nat) (counted : history.length≤B)
    (fields : RootPaper.TableCost.HistoryFieldBits B history) (cache : ReferenceReplayCache I)
    (visited : cache∈visitedCaches input available budget (referenceReplayInitial I) history) :
    SnapshotFields B (snapshotCalculation cache).1 := by
  obtain ⟨bounded,subset,_depths⟩:=initial_visited_data input available budget history cache visited
  rw [snapshotCalculation_value]
  exact snapshot_fields cache B (bounded.1.trans counted)
    (fun event inside n present=>fields event (subset.1 inside) n present)

def dataWidth (input : StatisticalInput I) (C : Contract I) (budget : Rat) (history : List (VisibleEvent I)) : Nat :=
  arithmeticScale input C budget+history.length+RootPaper.TableCost.historyMaterial history+16

def dataWidthRate : Nat := 27680

theorem native_dataWidth {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (early : C.reporting=.early) (accounting : NormalAccounting I)
    (policy : Policy input C .native accounting Seed) (available : Finset I.Tool) (budget : Rat)
    (sample : Seed×input.World) (clock : Nat) (within : clock≤4*arithmeticScale input C budget) :
    dataWidth input C budget (run input C .native accounting policy.rule sample clock).history≤
      dataWidthRate*(arithmeticScale input C budget)^3 := by
  let P:=arithmeticScale input C budget
  have positive : 1≤P := by dsimp only [P,arithmeticScale];omega
  have original : inputSize input C budget≤P := by dsimp only [P,arithmeticScale];omega
  have size : inputSize input C budget+clock+1≤6*P := by omega
  have inputBits:=(RootB23HistoryBits.run_controllerInput_length_le input C .native accounting
    policy.rule policy.legal sample clock available budget).trans
      (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left size 3))
  have material:= (RootPaper.TableCost.history_material_input input C available budget
    (run input C .native accounting policy.rule sample clock).history).trans inputBits
  have scaled : RootPaper.TableCost.historyMaterial (run input C .native accounting policy.rule sample clock).history≤27648*P^3 := by
    simpa only [mul_pow,←Nat.mul_assoc,show 128*(6 : Nat)^3=27648 from by decide] using material
  have count:=(run_history_length input C early .native accounting policy sample clock).trans
    (Nat.mul_le_mul_left 2 within)
  have linear:=RootB23HistoryBits.cubic_dominates P positive
  dsimp only [dataWidth,dataWidthRate]
  change P+_+_+16≤27680*P^3
  nlinarith only [scaled,count,linear.1,linear.2.2]

def originalHorizon (input : StatisticalInput I) (budget : Rat) : Nat :=
  quotaActionBound I (computedQuotas input budget)+1

theorem horizon_le_scale (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    originalHorizon input budget≤2*arithmeticScale input C budget := by
  unfold originalHorizon quotaActionBound arithmeticScale inputSize numericalQuota
  omega

end RootPaper.Reference.Charged
