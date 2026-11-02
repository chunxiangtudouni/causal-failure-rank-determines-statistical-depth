module
public import RootPaper_TableCost_Naturals010
public import RootPaper_TableCost_Cache008
public import RootPaper_TableCost_Fees009

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open CompactPrice PSTRTML01CacheRecord252 RationalControllerComputation PSTRWordBool
variable {I : Instance}

def WorkBounds (B : Nat) (work : Execution I) : Prop :=
  (∀ pair∈work.rationalTests,RatInput.Encoder.fieldSize pair.1+RatInput.Encoder.fieldSize pair.2≤8*B+8) ∧
  (∀ pair∈work.naturalTests,NatPairBound B pair) ∧
  (∀ read∈work.historyReads,read.length≤2*B)

theorem targetAt_rat_bits (cache : ReferenceReplayCache I) (kind : Option ReferenceBudgetCase)
    (current : Option Rat) (S : Nat)
    (widths : ∀ risk,current=some risk→RatInput.Encoder.fieldSize risk≤S) :
    ∀ pair∈(targetAt kind current cache).rationalTests,
      RatInput.Encoder.fieldSize pair.1+RatInput.Encoder.fieldSize pair.2≤S+4 := by
  unfold targetAt
  split
  · intro pair member;cases member
  · cases kind with
    | none => cases current <;> intro pair member <;> cases member
    | some kind =>
      cases current with
      | none => intro pair member;cases member
      | some risk =>
        have width:=widths risk rfl
        intro pair member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl
        · change RatInput.Encoder.fieldSize risk+2≤S+4;omega
        · change RatInput.Encoder.fieldSize risk+RatInput.Encoder.fieldSize (1/(4:Rat))≤S+4
          have quarter : RatInput.Encoder.fieldSize (1/(4:Rat))=4:=RootPaper.BudgetCost.field_quarter
          rw [quarter];omega

theorem targetAt_nat_bits (cache : ReferenceReplayCache I) (kind : Option ReferenceBudgetCase)
    (current : Option Rat) (B : Nat) (events : cache.events.length≤B) (stages : I.stageCount≤B) :
    ∀ pair∈(targetAt kind current cache).naturalTests,NatPairBound B pair := by
  unfold targetAt
  split
  · intro pair member;cases member
  · cases kind with
    | none => cases current <;> intro pair member <;> cases member
    | some kind =>
      cases current with
      | none => intro pair member;cases member
      | some risk =>
        intro pair member
        cases List.mem_singleton.mp member
        exact natural_pair B _ _ ((natBits_le_value _).trans (by omega)) ((natBits_le_value _).trans (by omega))

theorem kernel_control (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I) (B : Nat)
    (valid : 0<budget ∧ budget≤1/2) (width : RatInput.Encoder.fieldSize budget≤B)
    (bounded : CacheBound B cache) (stages : I.stageCount≤B) :
    (∀ pair∈(kernel budget records cache).rationalTests,
      RatInput.Encoder.fieldSize pair.1+RatInput.Encoder.fieldSize pair.2≤8*B+8) ∧
    (∀ pair∈(kernel budget records cache).naturalTests,NatPairBound B pair) := by
  have widths : ∀ risk,(RootPaper.Reference.budgetWork (I:=I) (budget/2) cache.events).1=some risk→
      RatInput.Encoder.fieldSize risk≤8*B+4 := by
    intro risk actual
    rw [RootPaper.Reference.budgetWork_value] at actual
    have old:=RootB236.RiskFold.original_path_width budget cache.events risk valid actual
    have events:=bounded.2.2
    omega
  exact ⟨targetAt_rat_bits cache (recordKindAtCache records cache) _ _ widths,
    targetAt_nat_bits cache (recordKindAtCache records cache) _ B bounded.2.2 stages⟩

theorem body_read_lengths (input : StatisticalInput I) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (data : Kernel I) (B : Nat)
    (seen : cache.seen.length≤B) (material : instanceMaterial input≤B) (tools : I.toolCount≤B) :
    ∀ read∈(body input available cache event data).historyReads,read.length≤B := by
  unfold body
  split
  · intro read member;cases member
  · cases event
    all_goals intro read member
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals repeat' rcases member with member|member
    all_goals dsimp only
    all_goals omega

theorem step_control (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (cache : ReferenceReplayCache I) (event : VisibleEvent I) (B : Nat)
    (valid : 0<budget ∧ budget≤1/2) (width : RatInput.Encoder.fieldSize budget≤B)
    (bounded : CacheBound B cache) (fields : HistoryFieldBits B cache.seen) (eventFields : FieldBits B event)
    (stages : I.stageCount≤B) (tools : I.toolCount≤B) (material : instanceMaterial input≤B)
    (alphabets : ∀ stage,natBits (input.experiment stage).alphabetSize≤B+1) :
    WorkBounds B (step input available budget records cache event) := by
  have data:=kernel_control budget records cache B valid width bounded stages
  have index : natBits (kernel budget records cache).archiveIndex≤B+1 := by
    have count : historyCursor cache.seen≤cache.seen.length:=List.length_filterMap_le _ _
    have bits:=natBits_le_value (historyCursor cache.seen)
    change natBits (historyCursor cache.seen)≤B+1
    have seen:=bounded.1
    omega
  refine ⟨data.1,?_,?_⟩
  · intro pair member
    change pair∈(kernel budget records cache).naturalTests++(body input available cache event (kernel budget records cache)).naturalTests at member
    rcases List.mem_append.mp member with front|next
    · exact data.2 pair front
    · exact body_natural_bits input available cache event (kernel budget records cache) B bounded fields eventFields stages tools alphabets index pair next
  · intro read member
    change read∈⟨HistoryHelper.cursor,cache.seen.length⟩::(body input available cache event (kernel budget records cache)).historyReads at member
    rcases List.mem_cons.mp member with rfl|next
    · have seen:=bounded.1;dsimp only;omega
    · exact (body_read_lengths input available cache event (kernel budget records cache) B bounded.1 material tools read next).trans (by omega)

theorem join_control (B : Nat) (front later : Execution I) (a : WorkBounds B front) (b : WorkBounds B later) :
    WorkBounds B (join front later) := by
  refine ⟨?_,?_,?_⟩
  · intro pair member;rcases List.mem_append.mp member with member|member
    · exact a.1 pair member
    · exact b.1 pair member
  · intro pair member;rcases List.mem_append.mp member with member|member
    · exact a.2.1 pair member
    · exact b.2.1 pair member
  · intro read member;rcases List.mem_append.mp member with member|member
    · exact a.2.2 read member
    · exact b.2.2 read member

theorem replayFrom_control (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (whole history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (B limit : Nat) (valid : 0<budget ∧ budget≤1/2) (width : RatInput.Encoder.fieldSize budget≤B)
    (bounded : CacheBound limit cache) (room : limit+history.length≤B)
    (subset : CacheSubset whole cache) (remaining : history⊆whole) (fields : HistoryFieldBits B whole)
    (stages : I.stageCount≤B) (tools : I.toolCount≤B) (material : instanceMaterial input≤B)
    (alphabets : ∀ stage,natBits (input.experiment stage).alphabetSize≤B+1) :
    WorkBounds B (replayFrom input available budget records cache history) := by
  induction history generalizing cache limit with
  | nil =>
      refine ⟨?_,?_,?_⟩
      all_goals intro value member;cases member
  | cons event later ih =>
      have before : CacheBound B cache:=cacheBound_mono cache (by omega) bounded
      have present:event∈whole:=remaining List.mem_cons_self
      have front:=step_control input available budget records cache event B valid width before
        (fun e member=>fields e (subset.1 member)) (fields event present) stages tools material alphabets
      simp only [replayFrom]
      cases finished:(step input available budget records cache event).result with
      | none => exact front
      | some next =>
          apply join_control B _ _ front
          exact ih next (limit+1)
            (step_cacheBound input available budget records cache next event limit bounded finished)
            (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using room)
            (step_cacheSubset input available budget records cache next event whole subset present finished)
            (fun e member=>remaining (List.mem_cons_of_mem _ member))

theorem replay_control (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (history : List (VisibleEvent I)) (B : Nat)
    (valid : 0<budget ∧ budget≤1/2) (width : RatInput.Encoder.fieldSize budget≤B)
    (room : history.length≤B) (fields : HistoryFieldBits B history)
    (stages : I.stageCount≤B) (tools : I.toolCount≤B) (material : instanceMaterial input≤B)
    (alphabets : ∀ stage,natBits (input.experiment stage).alphabetSize≤B+1) :
    WorkBounds B (replay input available budget records history) := by
  have initial : CacheBound 0 (referenceReplayInitial I) := by
    simp only [CacheBound,referenceReplayInitial,List.length_nil];omega
  have subset : CacheSubset history (referenceReplayInitial I) := by
    constructor
    all_goals intro e member;cases member
  have runBounds:=replayFrom_control input available budget records history history (referenceReplayInitial I) B 0 valid width initial
    (by simpa only [Nat.zero_add] using room) subset (fun _ member=>member) fields stages tools material alphabets
  have guards : ∀ pair∈([(budget,0),(budget,1/2)] : List (Rat×Rat)),
      RatInput.Encoder.fieldSize pair.1+RatInput.Encoder.fieldSize pair.2≤8*B+8 := by
    intro pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · change RatInput.Encoder.fieldSize budget+2≤8*B+8;omega
    · have half : RatInput.Encoder.fieldSize (1/(2:Rat))=3 := by
        rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
        norm_num [RootB23.WordOddsBits.width,natBits]
      change RatInput.Encoder.fieldSize budget+RatInput.Encoder.fieldSize (1/(2:Rat))≤8*B+8
      rw [half];omega
  unfold replay
  dsimp only
  rw [ite_eq_left valid]
  cases finished:(replayFrom input available budget records (referenceReplayInitial I) history).result with
  | none =>
      refine ⟨?_,runBounds.2.1,runBounds.2.2⟩
      intro pair member
      rcases List.mem_append.mp member with new|old
      · exact guards pair new
      · exact runBounds.1 pair old
  | some cache =>
      have cacheBound : CacheBound B cache:=cacheBound_mono cache room
        (by simpa only [Nat.zero_add] using replayFrom_cacheBound input available budget records (referenceReplayInitial I) cache history 0 initial finished)
      have eventBits:=natBits_le_value cache.events.length
      have cursor : historyCursor cache.seen≤cache.seen.length:=List.length_filterMap_le _ _
      have cursorBits:=natBits_le_value (historyCursor cache.seen)
      have stageBits:=natBits_le_value I.stageCount
      refine ⟨?_,?_,?_⟩
      · intro pair member
        rcases List.mem_append.mp member with new|old
        · exact guards pair new
        · exact runBounds.1 pair old
      · intro pair member
        rcases List.mem_append.mp member with old|new
        · exact runBounds.2.1 pair old
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at new
          rcases new with rfl|rfl
          · exact natural_pair B _ _ (by have e:=cacheBound.2.2;omega) (by omega)
          · exact natural_pair B _ _ (by have s:=cacheBound.1;omega) (by omega)
      · intro read member
        rcases List.mem_append.mp member with old|new
        · exact runBounds.2.2 read old
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at new
          rcases new with rfl|rfl|rfl
          all_goals dsimp only
          all_goals have s:=cacheBound.1
          all_goals have e:=cacheBound.2.2
          all_goals omega

end RootPaper.TableCost
