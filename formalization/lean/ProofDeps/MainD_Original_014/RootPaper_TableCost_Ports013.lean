module
public import RootPaper_TableCost_Input011
public import RootPaper_TableCost_Coverage012

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open CompactPrice PSTRTML01CacheRecord252 PSTRTableRecordPlanner RationalControllerComputation PSTRWordBool
variable {I : Instance}

theorem observation_bits (history : List (VisibleEvent I)) (stage : I.Stage) (B : Nat)
    (fields : HistoryFieldBits B history) (symbol : Nat) (member : symbol∈historyObservations history stage) : natBits symbol≤B := by
  obtain ⟨event,present,selected⟩:=List.mem_filterMap.mp member
  cases event with
  | observation i value =>
      simp only [eventObservation] at selected
      split_ifs at selected
      cases Option.some.inj selected
      exact fields _ present _ (by simp [encodeEvent])
  | wrote | report | committed | executed | advanced | stopped | abandoned => cases selected

theorem bare_control (input : StatisticalInput I) (cache : ReferenceReplayCache I) (B : Nat)
    (action : Action I) (ticks : Nat) : WorkBounds B (decisionExecution cache (bare input action ticks)) := by
  refine ⟨?_,?_,?_⟩
  all_goals intro value member;cases member

theorem testing_control (input : StatisticalInput I) (quota : I.Stage→Nat) (cache : ReferenceReplayCache I)
    (data : Kernel I) (stage : I.Stage) (B : Nat) (bounded : cache.seen.length≤B)
    (fields : HistoryFieldBits B cache.seen) (stages : I.stageCount≤B) (material : instanceMaterial input≤B)
    (alphabets : ∀ i,(input.experiment i).alphabetSize≤B) (quotas : ∀ i,quota i≤B) :
    WorkBounds B (decisionExecution cache (testing input (some quota) cache data stage)) := by
  have count : (historyObservations cache.seen stage).length≤cache.seen.length:=List.length_filterMap_le _ _
  have listBits : ∀ pair∈(historyObservations cache.seen stage).map (fun symbol=>(symbol,(input.experiment stage).alphabetSize)),
      NatPairBound B pair := by
    intro pair member
    obtain ⟨symbol,present,rfl⟩:=List.mem_map.mp member
    exact natural_pair B _ _ ((observation_bits _ _ B fields symbol present).trans (by omega))
      ((natBits_le_value _).trans (by have alphabet:=alphabets stage;omega))
  have quotaBits:=natBits_le_value (quota stage)
  have lengthBits:=natBits_le_value (historyObservations cache.seen stage).length
  unfold testing
  cases data.kind with
  | none => exact bare_control input cache B _ _
  | some kind =>
    cases kind with
    | infiniteRank => exact bare_control input cache B _ _
    | noTool | finiteBad depth =>
      cases data.target with
      | none => exact bare_control input cache B _ _
      | some target =>
        refine ⟨?_,?_,?_⟩
        · intro pair member;cases member
        · intro pair member
          dsimp only [decisionExecution] at member
          split_ifs at member
          all_goals try exact listBits pair member
          all_goals rcases List.mem_append.mp member with old|new
          all_goals try exact listBits pair old
          all_goals cases List.mem_singleton.mp new
          all_goals exact natural_pair B _ _ (by omega) (by have q:=quotas stage;omega)
        · intro read member
          dsimp only [decisionExecution] at member
          split_ifs at member
          all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          all_goals rcases member with rfl|rfl
          all_goals dsimp only
          all_goals omega

theorem testing_word_origin (input : StatisticalInput I) (limit : ReferenceObservationLimit I)
    (cache : ReferenceReplayCache I) (data : Kernel I) (stage : I.Stage) (call : WordCall input)
    (member : call∈(testing input limit cache data stage).words) :
    data.target=some call.target ∧ call.word.1≤cache.seen.length := by
  unfold testing at member
  cases kindEq:data.kind with
  | none => simp only [kindEq] at member;cases member
  | some kind =>
    simp only [kindEq] at member
    cases kind with
    | infiniteRank => cases member
    | noTool | finiteBad depth =>
      cases targetEq:data.target with
      | none => simp only [targetEq] at member;cases member
      | some target =>
        simp only [targetEq] at member
        cases limitEq:limit
        all_goals simp only [limitEq] at member
        all_goals split_ifs at member
        all_goals simp at member
        all_goals cases member
        all_goals exact ⟨rfl,List.length_filterMap_le _ _⟩

theorem kernel_target_width (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I)
    (B : Nat) (valid : 0<budget ∧ budget≤1/2) (width : RatInput.Encoder.fieldSize budget≤B)
    (events : cache.events.length≤B) (archive : records.sum≤B) (target : Rat)
    (selected : (kernel budget records cache).target=some target) :
    RatInput.Encoder.fieldSize target≤6144*(B+1) := by
  rw [(kernel_values budget records cache).2.2.2] at selected
  unfold recordTarget at selected
  split at selected
  · cases selected
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at selected
    obtain ⟨kind,kindEq,current,currentEq,selected⟩:=selected
    split_ifs at selected
    have path : (referenceBudgetPath (budget/2) cache.events).bind (referenceBudgetTarget kind)=some target := by
      change referenceBudgetPath (budget/2) cache.events=some current at currentEq
      rw [currentEq,Option.bind_some]
      exact selected
    have depth:=archive_kind_depth I.toolCount records _ kind kindEq
    have bound:=RootB236.RiskFold.original_target_width budget cache.events kind target valid path
    omega

theorem replayFrom_subset (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (whole history : List (VisibleEvent I)) (cache next : ReferenceReplayCache I)
    (old : CacheSubset whole cache) (remaining : history⊆whole)
    (finished : (replayFrom input available budget records cache history).result=some next) : CacheSubset whole next := by
  induction history generalizing cache with
  | nil => cases Option.some.inj finished;exact old
  | cons event later ih =>
      simp only [replayFrom] at finished
      cases one:(step input available budget records cache event).result with
      | none => simp only [one] at finished;cases finished
      | some child =>
          simp only [one,join] at finished
          exact ih child (step_cacheSubset input available budget records cache child event whole old (remaining List.mem_cons_self) one)
            (fun e member=>remaining (List.mem_cons_of_mem _ member)) finished

theorem replay_subset (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (finished : (replay input available budget records history).result=some cache) : CacheSubset history cache := by
  have initial : CacheSubset history (referenceReplayInitial I) := by
    constructor
    all_goals intro e member;cases member
  unfold replay at finished
  dsimp only at finished
  split at finished
  · cases run:(replayFrom input available budget records (referenceReplayInitial I) history).result with
    | none => simp only [run] at finished;cases finished
    | some next =>
        simp only [run] at finished
        split_ifs at finished
        cases Option.some.inj finished
        exact replayFrom_subset input available budget records history history (referenceReplayInitial I) cache initial (fun _ member=>member) run
  · cases finished

theorem decision_control (input : StatisticalInput I) (quota : I.Stage→Nat) (history : List (VisibleEvent I))
    (cache : ReferenceReplayCache I) (data : Kernel I) (B : Nat) (bounded : cache.seen.length≤B)
    (fields : HistoryFieldBits B cache.seen) (room : history.length≤B)
    (stages : I.stageCount≤B) (material : instanceMaterial input≤B)
    (alphabets : ∀ i,(input.experiment i).alphabetSize≤B) (quotas : ∀ i,quota i≤B) :
    WorkBounds B (decisionExecution cache (decisionBody input (some quota) history cache data)) := by
  unfold decisionBody
  cases cache.halted with
  | true => exact bare_control input cache B _ _
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    cases stageAt data with
    | none =>
      have cursor:historyCursor history≤history.length:=List.length_filterMap_le _ _
      have bits:=natBits_le_value (historyCursor history)
      have stageBits:=natBits_le_value I.stageCount
      refine ⟨?_,?_,?_⟩
      · intro pair member;cases member
      · intro pair member;cases List.mem_singleton.mp member
        exact natural_pair B _ _ (by omega) (by omega)
      · intro read member;cases List.mem_singleton.mp member
        dsimp only;omega
    | some stage =>
      dsimp only
      cases cache.phase with
      | testing => exact testing_control input quota cache data stage B bounded fields stages material alphabets quotas
      | written => exact bare_control input cache B _ _
      | executed tool => exact bare_control input cache B _ _
      | reported =>
        dsimp only
        split_ifs
        all_goals refine ⟨?_,?_,?_⟩
        all_goals intro value member
        all_goals simp only [decisionExecution,List.mem_cons,List.not_mem_nil,or_false] at member
        all_goals repeat' rcases member with member|member
        all_goals dsimp only
        all_goals omega
      | allocated tool =>
        refine ⟨?_,?_,?_⟩
        all_goals intro value member
        all_goals simp only [decisionExecution,List.mem_singleton,List.not_mem_nil] at member
        all_goals cases member
        all_goals dsimp only
        all_goals omega

theorem decision_word_origin (input : StatisticalInput I) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I) (data : Kernel I) (call : WordCall input)
    (member : call∈(decisionBody input limit history cache data).words) :
    data.target=some call.target ∧ call.word.1≤cache.seen.length := by
  unfold decisionBody at member
  split at member
  · cases member
  · cases stageEq:stageAt data with
    | none => simp only [stageEq] at member;cases member
    | some stage =>
      simp only [stageEq] at member
      cases phaseEq:cache.phase with
      | testing => simp only [phaseEq] at member;exact testing_word_origin input limit cache data stage call member
      | written | executed tool => simp only [phaseEq] at member;cases member
      | allocated tool => simp only [phaseEq] at member;cases member
      | reported => simp only [phaseEq] at member;split_ifs at member <;> cases member

theorem prepared_quota_reads_paid (input : StatisticalInput I) (C : Contract I) (budget : Rat)
    (positive : 0<budget) (stage : I.Stage) :
    (RootPaper.B23.readQuota (RootPaper.Prep.preparationCalculation input C budget positive).value.rows stage.val).2≤
      (HistoryRead.mk .experiment (instanceMaterial input+I.stageCount)).visits := by
  have actual:=(RootPaper.B23.actual_prepared_quota_view input C budget positive stage).2
  change _≤ instanceMaterial input+I.stageCount+1
  omega

end RootPaper.TableCost
