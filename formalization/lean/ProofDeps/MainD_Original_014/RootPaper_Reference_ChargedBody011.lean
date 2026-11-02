module
public import RootPaper_Reference_ChargedState010

/-! A dedicated cache-step calculation. All unbounded traversals use their
charged return values. The fixed local units below cover only a bounded
number of field accesses, finite-tag tests, numeric guards and record fields;
their binary price is a separate closed scalar/data-width bound. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference
variable {I : Instance}

def executed (phase : ReferenceReplayPhase I) : Bool :=
  match phase with | .executed _ => true | _ => false

theorem executed_iff (phase : ReferenceReplayPhase I) :
    executed phase=true ↔ ∃ tool,phase=.executed tool := by cases phase <;> simp [executed]

def reportError (view : Snapshot I) : VisibleEvent I→Bool
  | .report _ truth _ => decide (((view.written.map Prod.fst).getD false)≠truth)
  | _ => false

def bodyCalculation (input : StatisticalInput I) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (view : Snapshot I) (data : Kernel I)
    (recorded : ReferenceReplayCache I) (events : List ReferenceBudgetEvent) (reportCount : Nat) :
    Option (ReferenceReplayCache I)×Nat :=
  if cache.halted then (none,2) else
  match event with
  | .observation i symbol =>
      match view.stage with
      | none => (none,4)
      | some stage =>
          (if i=stage ∧ symbol<(input.experiment i).alphabetSize ∧ cache.phase=.testing ∧ data.target.isSome
            then some recorded else none,16)
  | .wrote i _ serial =>
      match view.stage,data.classification,data.current with
      | some stage,some _,some _ =>
          (if i=stage ∧ serial=view.actions ∧ cache.phase=.testing
            then some {recorded with phase:=.written} else none,16)
      | _,_,_ => (none,8)
  | .report i _ serial =>
      match view.stage,view.written,data.classification,data.current with
      | some stage,some written,some _,some _ =>
          (if i=stage ∧ serial=written.2 ∧ cache.phase=.written ∧ reportCount<I.stageCount
            then some {recorded with events:=events,phase:=.reported} else none,20)
      | _,_,_,_ => (none,8)
  | .committed handle tool =>
      match view.stage,data.current with
      | some stage,some _ =>
          let compatible:=probe tool (I.eligible stage)
          let already:=probe tool view.used
          let allowed:=probe tool available
          (if cache.phase=.reported ∧ view.mismatch handle ∧ compatible.1 ∧ !already.1 ∧ allowed.1 ∧ data.repair=some tool
            then some {recorded with phase:=.allocated tool} else none,compatible.2+already.2+allowed.2+24)
      | _,_ => (none,8)
  | .executed handle tool =>
      match view.stage with
      | none => (none,4)
      | some _ =>
          (if cache.phase=.allocated tool ∧ view.mismatch handle then some {recorded with phase:=.executed tool} else none,20)
  | .advanced i =>
      match view.stage,data.current with
      | some stage,some _ =>
          (if i=stage ∧ ((cache.phase=.reported ∧ view.correct) ∨ executed cache.phase)
            then some {recorded with entryHistory:=recorded.seen,phase:=.testing} else none,16)
      | _,_ => (none,8)
  | .stopped =>
      (if view.cursor=I.stageCount ∧ cache.phase=.testing then some {recorded with halted:=true} else none,12)
  | .abandoned =>
      (if cache.phase≠.written then some {recorded with halted:=true} else none,8)

private theorem probe_bound (tool : I.Tool) (items : Finset I.Tool) :
    (probe tool items).2≤3*I.toolCount+1 := by
  have count:=(probe_spec tool items).2
  have bounded : items.card≤I.toolCount := by simpa using Finset.card_le_univ items
  omega

private theorem three_probes (tool : I.Tool) (first second third : Finset I.Tool) :
    (probe tool first).2+(probe tool second).2+(probe tool third).2+24≤9*I.toolCount+64 := by
  have a:=probe_bound tool first
  have b:=probe_bound tool second
  have c:=probe_bound tool third
  omega

theorem bodyCalculation_value (input : StatisticalInput I) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (data : Kernel I) :
    (bodyCalculation input available cache event (RootPaper.Reference.snapshot cache) data
      {cache with seen:=cache.seen++[event]}
      (cache.events++[(data.classification.getD .infiniteRank,
        reportError (RootPaper.Reference.snapshot cache) event)]) cache.events.length).1=
      stepBody input available cache event data := by
  unfold bodyCalculation stepBody
  cases halted : cache.halted with
  | true => rfl
  | false =>
      dsimp only
      cases event with
      | observation stage symbol =>
          cases (RootPaper.Reference.snapshot cache).stage <;> rfl
      | wrote stage bit serial =>
          cases (RootPaper.Reference.snapshot cache).stage <;>
            cases data.classification <;> cases data.current <;> rfl
      | report stage truth serial =>
          cases current : (RootPaper.Reference.snapshot cache).stage <;>
            cases written : (RootPaper.Reference.snapshot cache).written <;>
            cases classified : data.classification <;> cases risk : data.current <;> first
            | rfl
            | (simp only [reportError,written];rfl)
      | committed handle tool =>
          cases (RootPaper.Reference.snapshot cache).stage <;> cases data.current <;> first
            | rfl
            | (dsimp only
               simp only [(probe_spec tool (I.eligible _)).1,
                 (probe_spec tool (RootPaper.Reference.snapshot cache).used).1,
                 (probe_spec tool available).1,decide_eq_true_eq,not_decide_eq_true]
               rfl)
      | executed handle tool =>
          cases (RootPaper.Reference.snapshot cache).stage <;> rfl
      | advanced stage =>
          cases (RootPaper.Reference.snapshot cache).stage <;> cases data.current <;> first
            | rfl
            | (simp only [executed_iff];rfl)
      | stopped => rfl
      | abandoned => rfl

theorem bodyCalculation_work (input : StatisticalInput I) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (view : Snapshot I) (data : Kernel I)
    (recorded : ReferenceReplayCache I) (events : List ReferenceBudgetEvent) (reportCount : Nat) :
    (bodyCalculation input available cache event view data recorded events reportCount).2≤9*I.toolCount+64 := by
  dsimp only [bodyCalculation]
  repeat' split
  all_goals first | omega | exact three_probes _ _ _ _

structure StepCalculation (I : Instance) where
  value : Option (ReferenceReplayCache I)
  ranks : List (RankCall I)
  scalar : List (ScalarCall I)
  administration : Nat

def stepCalculation (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) : StepCalculation I :=
  let view:=snapshotCalculation cache
  let data:=kernelCalculation available budget cache view.1
  let seen:=appendOne cache.seen event
  let reports:=appendOne cache.events
    ((data.1.classification.getD .infiniteRank),reportError view.1 event)
  let measured:=count cache.events
  let recorded:={cache with seen:=seen.1}
  let body:=bodyCalculation input available cache event view.1 data.1 recorded reports.1 measured.1
  ⟨body.1,data.1.ranks,data.1.scalar,
    view.2+data.2+seen.2+reports.2+measured.2+body.2+24⟩

theorem stepCalculation_value (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) :
    (stepCalculation input available budget cache event).value=
      referenceAvailableStep input available budget cache event := by
  have data:=kernelCalculation_value available budget cache (snapshotCalculation cache).1
    (snapshotCalculation_value cache)
  dsimp only [stepCalculation]
  rw [data]
  simp only [snapshotCalculation_value,(appendOne_spec _ _).1,(count_spec _).1]
  rw [bodyCalculation_value]
  exact stepValue_eq input available budget cache event

theorem stepCalculation_ranks (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) :
    (stepCalculation input available budget cache event).ranks=(kernel I available budget cache).ranks := by
  dsimp only [stepCalculation]
  rw [kernelCalculation_value _ _ _ _ (snapshotCalculation_value cache)]

theorem stepCalculation_scalar (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) :
    (stepCalculation input available budget cache event).scalar=(kernel I available budget cache).scalar := by
  dsimp only [stepCalculation]
  rw [kernelCalculation_value _ _ _ _ (snapshotCalculation_value cache)]

theorem stepCalculation_work (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) :
    (stepCalculation input available budget cache event).administration≤
      (6*I.toolCount+120)*(cache.seen.length+cache.entryHistory.length+cache.events.length+1)+
      2*(6*I.toolCount+12)*(I.toolCount+1)+9*I.toolCount+260 := by
  have view:=snapshotCalculation_work cache
  have data:=kernelCalculation_work available budget cache (snapshotCalculation cache).1
  have seen:=(appendOne_spec cache.seen event).2
  have reports:=(appendOne_spec cache.events
    (((kernelCalculation available budget cache (snapshotCalculation cache).1).1.classification.getD .infiniteRank),
      reportError (snapshotCalculation cache).1 event)).2
  have measured:=(count_spec cache.events).2
  have body:=bodyCalculation_work input available cache event (snapshotCalculation cache).1
    (kernelCalculation available budget cache (snapshotCalculation cache).1).1
    {cache with seen:=(appendOne cache.seen event).1}
    (appendOne cache.events
      (((kernelCalculation available budget cache (snapshotCalculation cache).1).1.classification.getD .infiniteRank),
        reportError (snapshotCalculation cache).1 event)).1 (count cache.events).1
  dsimp only [stepCalculation]
  nlinarith

end RootPaper.Reference.Charged
