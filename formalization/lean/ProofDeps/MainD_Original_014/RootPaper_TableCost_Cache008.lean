module
public import RootPaper_TableCost_Widths007

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open CompactPrice PSTRTML01CacheRecord252 PSTRTableRecordDecision
open RationalControllerComputation
variable {I : Instance}

theorem body_cacheDepth (input : StatisticalInput I) (available : Finset I.Tool)
    (records : List Nat) (cache next : ReferenceReplayCache I) (event : VisibleEvent I) (data : Kernel I)
    (old : CacheDepth records cache)
    (depths : ∀ kind,data.kind=some kind→RootB236.RiskFold.caseDepth kind≤records.sum)
    (finished : (body input available cache event data).result=some next) : CacheDepth records next := by
  unfold body at finished
  split at finished
  · cases finished
  · cases event
    all_goals dsimp only at finished
    all_goals try (simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at finished)
    all_goals repeat' rcases finished with ⟨_,_,finished⟩
    all_goals split_ifs at finished
    all_goals cases Option.some.inj finished
    all_goals dsimp only [CacheDepth] at old ⊢
    all_goals intro report present
    all_goals try exact old report present
    all_goals try (simp only [List.mem_append,List.mem_singleton] at present)
    all_goals rcases present with earlier|same
    all_goals try exact old report earlier
    all_goals cases same
    all_goals exact depths _ (by assumption)

theorem step_cacheDepth (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (old : CacheDepth records cache)
    (finished : (step input available budget records cache event).result=some next) : CacheDepth records next := by
  exact body_cacheDepth input available records cache next event (kernel budget records cache) old
    (fun kind selected=>archive_kind_depth I.toolCount records _ kind selected) finished

theorem targetAt_callBound (cache : ReferenceReplayCache I) (kind : Option ReferenceBudgetCase)
    (current : Option Rat) (S D : Nat)
    (widths : ∀ risk,current=some risk→PSTRWordBool.RatInput.Encoder.fieldSize risk≤S)
    (depths : ∀ selected,kind=some selected→RootB236.RiskFold.caseDepth selected≤D)
    (call : RootPaper.Reference.ScalarCall I) (member : call∈(targetAt kind current cache).calls) :
    CallBound S D call := by
  unfold targetAt at member
  split at member
  · cases member
  · cases kind with
    | none => cases current <;> cases member
    | some selected =>
      cases current with
      | none => cases member
      | some risk =>
        dsimp only at member
        split at member
        · rename_i valid
          have width:=widths risk rfl
          have depth:=depths selected rfl
          cases selected with
          | infiniteRank => cases member
          | noTool =>
              have same : call=.half risk:=List.mem_singleton.mp member
              subst call
              exact width
          | finiteBad d =>
              have same : call=.target risk d.val:=List.mem_singleton.mp member
              subst call
              exact ⟨valid.1,d.pos,width,depth⟩
        · cases member

theorem kernel_callBound (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I)
    (valid : 0<budget ∧ budget≤1/2) (depths : CacheDepth records cache)
    (call : RootPaper.Reference.ScalarCall I) (member : call∈(kernel budget records cache).calls) :
    CallBound (2*PSTRWordBool.RatInput.Encoder.fieldSize budget+6*cache.events.length+4) records.sum call := by
  let S:=2*PSTRWordBool.RatInput.Encoder.fieldSize budget+6*cache.events.length+4
  have widths : ∀ risk,(RootPaper.Reference.budgetWork (I:=I) (budget/2) cache.events).1=some risk→
      PSTRWordBool.RatInput.Encoder.fieldSize risk≤S := by
    intro risk actual
    rw [RootPaper.Reference.budgetWork_value] at actual
    exact RootB236.RiskFold.original_path_width budget cache.events risk valid actual
  have kindDepth : ∀ kind,recordKindAtCache records cache=some kind→RootB236.RiskFold.caseDepth kind≤records.sum :=
    fun kind selected=>archive_kind_depth I.toolCount records _ kind selected
  change call∈(.half budget::(RootPaper.Reference.budgetWork (I:=I) (budget/2) cache.events).2++
    (targetAt (recordKindAtCache records cache) _ cache).calls) at member
  simp only [List.mem_cons,List.mem_append] at member
  rcases member with front|target
  · rcases front with rfl|folded
    · change PSTRWordBool.RatInput.Encoder.fieldSize budget≤S
      dsimp only [S];omega
    · exact budgetWork_callBound budget cache.events records.sum valid depths call folded
  · exact targetAt_callBound cache (recordKindAtCache records cache) _ S records.sum widths kindDepth call target

theorem callBound_mono {S T D : Nat} (order : S≤T) (call : RootPaper.Reference.ScalarCall I)
    (bounded : CallBound S D call) : CallBound T D call := by
  cases call with
  | target risk depth => exact ⟨bounded.1,bounded.2.1,bounded.2.2.1.trans order,bounded.2.2.2⟩
  | budgetVisit kind error risk => exact ⟨bounded.1.trans order,bounded.2⟩
  | half risk => exact bounded.trans order
  | badRisk risk target => exact ⟨bounded.1.trans order,by dsimp only [CallBound] at bounded ⊢;omega⟩
  | word stage target length => exact bounded

theorem replayFrom_calls (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I)
    (history : List (VisibleEvent I)) (limit : Nat) (valid : 0<budget ∧ budget≤1/2)
    (bounded : CacheBound limit cache) (depths : CacheDepth records cache) :
    ∀ call∈(replayFrom input available budget records cache history).calls,
      CallBound (2*PSTRWordBool.RatInput.Encoder.fieldSize budget+6*(limit+history.length)+4) records.sum call := by
  induction history generalizing cache limit with
  | nil => intro call member;cases member
  | cons event later ih =>
      intro call member
      have front : ∀ call∈(step input available budget records cache event).calls,
          CallBound (2*PSTRWordBool.RatInput.Encoder.fieldSize budget+6*(limit+(event::later).length)+4) records.sum call := by
        intro call present
        exact callBound_mono (by have e:=bounded.2.2;simp only [List.length_cons];omega) call
          (kernel_callBound budget records cache valid depths call present)
      simp only [replayFrom] at member
      cases finished:(step input available budget records cache event).result with
      | none => simp only [finished] at member;exact front call member
      | some next =>
          simp only [finished,join,List.mem_append] at member
          rcases member with present|present
          · exact front call present
          · have tail:=ih next (limit+1)
              (step_cacheBound input available budget records cache next event limit bounded finished)
              (step_cacheDepth input available budget records cache next event depths finished) call present
            simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tail

theorem replayFrom_cacheDepth (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (cache next : ReferenceReplayCache I)
    (history : List (VisibleEvent I)) (depths : CacheDepth records cache)
    (finished : (replayFrom input available budget records cache history).result=some next) :
    CacheDepth records next := by
  induction history generalizing cache with
  | nil => cases Option.some.inj finished;exact depths
  | cons event later ih =>
      simp only [replayFrom] at finished
      cases one:(step input available budget records cache event).result with
      | none => simp only [one] at finished;cases finished
      | some child =>
          simp only [one,join] at finished
          exact ih child (step_cacheDepth input available budget records cache child event depths one) finished

theorem replay_cacheDepth (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (finished : (replay input available budget records history).result=some cache) : CacheDepth records cache := by
  have initial : CacheDepth records (referenceReplayInitial I) := by intro event present;cases present
  unfold replay at finished
  dsimp only at finished
  split at finished
  · cases run:(replayFrom input available budget records (referenceReplayInitial I) history).result with
    | none => simp only [run] at finished;cases finished
    | some next =>
        simp only [run] at finished
        split_ifs at finished
        cases Option.some.inj finished
        exact replayFrom_cacheDepth input available budget records (referenceReplayInitial I) cache history initial run
  · cases finished

theorem replay_calls (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (history : List (VisibleEvent I)) (valid : 0<budget ∧ budget≤1/2) :
    ∀ call∈(replay input available budget records history).calls,
      CallBound (2*PSTRWordBool.RatInput.Encoder.fieldSize budget+6*history.length+4) records.sum call := by
  have bounded : CacheBound 0 (referenceReplayInitial I) := by
    simp only [CacheBound,referenceReplayInitial,List.length_nil];omega
  have depths : CacheDepth records (referenceReplayInitial I) := by intro event present;cases present
  have result:=replayFrom_calls input available budget records (referenceReplayInitial I) history 0 valid bounded depths
  unfold replay
  dsimp only
  rw [ite_eq_left valid]
  cases (replayFrom input available budget records (referenceReplayInitial I) history).result <;>
    simpa only [Nat.zero_add] using result

end RootPaper.TableCost
