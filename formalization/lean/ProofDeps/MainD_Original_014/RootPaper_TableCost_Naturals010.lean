module
public import RootPaper_TableCost_Candidate006
public import RootPaper_TableCost_Widths007

/-! Binary guard operands come from the original input/history or from
already bounded list lengths. In particular getLast? does not introduce
an unaccounted write-serial field. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open RationalControllerComputation
variable {I : Instance}

def historyMaterial (history : List (VisibleEvent I)) : Nat :=
  ((history.flatMap encodeEvent).flatMap encodeDatum).length

def FieldBits (B : Nat) (event : VisibleEvent I) : Prop :=
  ∀ n,Datum.natural n∈encodeEvent event→natBits n≤B

def HistoryFieldBits (B : Nat) (history : List (VisibleEvent I)) : Prop :=
  ∀ event∈history,FieldBits B event

theorem natBits_le_value (n : Nat) : natBits n≤n+1 := by
  simpa only [natBits,Nat.log2_eq_log_two] using Nat.add_le_add_right (Nat.log_le_self 2 n) 1

theorem datum_material (data : List Datum) (datum : Datum) (member : datum∈data) :
    (encodeDatum datum).length≤(data.flatMap encodeDatum).length := by
  induction data with
  | nil => cases member
  | cons front later ih =>
      simp only [List.mem_cons] at member
      simp only [List.flatMap_cons,List.length_append]
      rcases member with rfl|inside
      · omega
      · exact (ih inside).trans (by omega)

theorem history_material_fields (history : List (VisibleEvent I)) :
    HistoryFieldBits (historyMaterial history) history := by
  intro event present n member
  have bound:=datum_material (history.flatMap encodeEvent) (.natural n)
    (List.mem_flatMap.mpr ⟨event,present,member⟩)
  rw [PSTRTMLength004.encodeDatum_natural_length] at bound
  change 2*natBits n+2≤historyMaterial history at bound
  omega

theorem written_serial_bits (history : List (VisibleEvent I)) (stage : I.Stage) (B : Nat)
    (fields : HistoryFieldBits B history) : natBits (((historyWrite history stage).map Prod.snd).getD 0)≤B+1 := by
  cases found:historyWrite history stage with
  | none => simp only [Option.map_none,Option.getD_none];change 1≤B+1;omega
  | some written =>
      have present : written∈history.filterMap (eventWrite stage) := List.mem_of_getLast? found
      obtain ⟨event,inside,selected⟩:=List.mem_filterMap.mp present
      cases event with
      | wrote j bit serial =>
          simp only [eventWrite] at selected
          split_ifs at selected
          · have same:=congrArg Prod.snd (Option.some.inj selected)
            have bound:=fields (.wrote j bit serial) inside serial (by simp [encodeEvent])
            simp only [Option.map_some,Option.getD_some,←same]
            omega
      | observation | report | committed | executed | advanced | stopped | abandoned => cases selected

def NatPairBound (B : Nat) (pair : Nat×Nat) : Prop := natBits pair.1+natBits pair.2+1≤2*B+3

theorem natural_pair (B a b : Nat) (left : natBits a≤B+1) (right : natBits b≤B+1) : NatPairBound B (a,b) := by
  change natBits a+natBits b+1≤2*B+3
  omega

theorem body_natural_bits (input : StatisticalInput I) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) (data : Kernel I) (B : Nat)
    (bounded : CacheBound B cache) (fields : HistoryFieldBits B cache.seen) (eventFields : FieldBits B event)
    (stages : I.stageCount≤B) (tools : I.toolCount≤B)
    (alphabets : ∀ stage,natBits (input.experiment stage).alphabetSize≤B+1)
    (index : natBits data.archiveIndex≤B+1) :
    ∀ pair∈(body input available cache event data).naturalTests,NatPairBound B pair := by
  have seenB:=bounded.1
  have eventsB:=bounded.2.2
  have stageBits : ∀ stage : I.Stage,natBits stage.val≤B+1 := by
    intro stage;have bits:=natBits_le_value stage.val;have below:stage.val<I.stageCount:=stage.isLt;omega
  have toolBits : ∀ tool : I.Tool,natBits tool.val≤B+1 := by
    intro tool;have bits:=natBits_le_value tool.val;have below:=tool.isLt;omega
  have stageCount:=natBits_le_value I.stageCount
  have toolCount:=natBits_le_value I.toolCount
  have events:=natBits_le_value cache.events.length
  have actionLength : (historyActions cache.seen).length≤cache.seen.length := List.length_filterMap_le _ _
  have actions:=natBits_le_value (historyActions cache.seen).length
  have written:=fun stage=>written_serial_bits cache.seen stage B fields
  unfold body
  split
  · intro pair member;cases member
  · cases event with
    | observation i symbol =>
        have symbolBits:=eventFields symbol (by simp [encodeEvent])
        dsimp only
        cases stageAt data with
        | none => intro pair member;cases member
        | some stage =>
            intro pair member
            simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl|rfl
            · exact natural_pair B _ _ (stageBits i) (stageBits stage)
            · exact natural_pair B _ _ (by omega) (alphabets i)
    | wrote i bit serial =>
        have serialBits:=eventFields serial (by simp [encodeEvent])
        dsimp only
        cases stageAt data with
        | none => intro pair member;cases List.mem_singleton.mp member;exact natural_pair B _ _ (by omega) (by omega)
        | some stage =>
            intro pair member
            simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl|rfl
            · exact natural_pair B _ _ (stageBits i) (stageBits stage)
            · exact natural_pair B _ _ (by omega) (by omega)
    | report i bit serial =>
        have serialBits:=eventFields serial (by simp [encodeEvent])
        dsimp only
        cases stageAt data with
        | none => intro pair member;cases member
        | some stage =>
            intro pair member
            simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl|rfl|rfl
            · exact natural_pair B _ _ (stageBits i) (stageBits stage)
            · exact natural_pair B _ _ (by omega) (written stage)
            · exact natural_pair B _ _ (by have e:=bounded.2.2;omega) (by omega)
    | committed handle tool | executed handle tool =>
        intro pair member
        cases List.mem_singleton.mp member
        exact natural_pair B _ _ (toolBits tool) (by omega)
    | advanced i =>
        dsimp only
        cases stageAt data with
        | none => intro pair member;cases member
        | some stage =>
            intro pair member
            cases List.mem_singleton.mp member
            exact natural_pair B _ _ (stageBits i) (stageBits stage)
    | stopped =>
        intro pair member
        cases List.mem_singleton.mp member
        exact natural_pair B _ _ index (by omega)
    | abandoned => intro pair member;cases member

def CacheSubset (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I) : Prop :=
  cache.seen⊆history ∧ cache.entryHistory⊆history

theorem step_cacheSubset (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : Rat) (records : List Nat) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (history : List (VisibleEvent I)) (old : CacheSubset history cache) (present : event∈history)
    (finished : (step input available budget records cache event).result=some next) : CacheSubset history next := by
  rw [step_result] at finished
  have extended : cache.seen++[event]⊆history := by
    intro e member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with before|rfl
    · exact old.1 before
    · exact present
  unfold PSTRTML01RecordReplay253.recordStep at finished
  split at finished
  · cases finished
  · cases event
    all_goals dsimp only at finished
    all_goals try (simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at finished)
    all_goals repeat' rcases finished with ⟨_,_,finished⟩
    all_goals split_ifs at finished
    all_goals cases Option.some.inj finished
    all_goals first | exact ⟨extended,old.2⟩ | exact ⟨extended,extended⟩

end RootPaper.TableCost
