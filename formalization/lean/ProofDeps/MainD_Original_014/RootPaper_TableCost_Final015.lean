module
public import RootPaper_TableCost_Ports013
public import RootPaper_TableCost_Aggregate014
public import RootPaper_TableCost_Helper016

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.TableCost
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Statistics
open CompactPrice PSTRTML01CacheRecord252 RationalControllerComputation PSTRWordBool
open scoped BigOperators
variable {I : Instance}

theorem callBound_widen {S T D E : Nat} (risk : S≤T) (depth : D≤E)
    (call : RootPaper.Reference.ScalarCall I) (old : CallBound S D call) : CallBound T E call := by
  cases call with
  | budgetVisit kind error value => exact ⟨old.1.trans risk,old.2.trans depth⟩
  | half value => exact old.trans risk
  | target value d => exact ⟨old.1,old.2.1,old.2.2.1.trans risk,old.2.2.2.trans depth⟩
  | badRisk value target => exact ⟨old.1.trans risk,by have a:=old.2;omega⟩
  | word stage target length => exact old.elim

theorem candidate_calls (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I)) (records : List Nat) (B : Nat)
    (valid : 0<budget ∧ budget≤1/2) (width : RatInput.Encoder.fieldSize budget≤B)
    (room : history.length≤B) (archive : records.sum≤B) :
    ∀ call∈(candidate input available budget limit history records).work.calls,CallBound (8*B+4) B call := by
  have earlier:=replay_calls input available budget records history valid
  unfold candidate
  dsimp only
  cases finished:(replay input available budget records history).result with
  | none =>
      intro call member
      exact callBound_widen (by omega) archive call (earlier call member)
  | some cache =>
      have bounded:=replay_cacheBound input available budget records history cache finished
      have depths:=replay_cacheDepth input available budget records history cache finished
      intro call member
      change call∈(replay input available budget records history).calls++((kernel budget records cache).calls++[]) at member
      rw [List.append_nil] at member
      rcases List.mem_append.mp member with before|current
      · exact callBound_widen (by omega) archive call (earlier call before)
      · have e:=bounded.2.2
        exact callBound_widen (by omega) archive call (kernel_callBound budget records cache valid depths call current)

theorem candidate_control (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat) (history : List (VisibleEvent I)) (records : List Nat) (B : Nat)
    (valid : 0<budget ∧ budget≤1/2) (width : RatInput.Encoder.fieldSize budget≤B)
    (room : history.length≤B) (fields : HistoryFieldBits B history)
    (stages : I.stageCount≤B) (tools : I.toolCount≤B) (material : instanceMaterial input≤B)
    (alphabets : ∀ stage,(input.experiment stage).alphabetSize≤B) (quotas : ∀ stage,quota stage≤B) :
    WorkBounds B (candidate input available budget (some quota) history records).work := by
  have alphabetBits : ∀ stage,natBits (input.experiment stage).alphabetSize≤B+1 :=
    fun stage=>(natBits_le_value _).trans (by have a:=alphabets stage;omega)
  have earlier:=replay_control input available budget records history B valid width room fields stages tools material alphabetBits
  unfold candidate
  dsimp only
  cases finished:(replay input available budget records history).result with
  | none => exact earlier
  | some cache =>
      have bounded:=cacheBound_mono cache room (replay_cacheBound input available budget records history cache finished)
      have subset:=replay_subset input available budget records history cache finished
      have data:=kernel_control budget records cache B valid width bounded stages
      have front : WorkBounds B (kernelExecution cache (kernel budget records cache)) := by
        refine ⟨data.1,data.2,?_⟩
        intro read member
        cases List.mem_singleton.mp member
        change cache.seen.length≤2*B
        have s:=bounded.1;omega
      have tail:=decision_control input quota history cache (kernel budget records cache) B bounded.1
        (fun event present=>fields event (subset.1 present)) room stages material alphabets quotas
      exact join_control B _ _ earlier (join_control B _ _ front tail)

theorem candidate_words (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool) (budget : Rat)
    (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I)) (records : List Nat) (B : Nat)
    (valid : 0<budget ∧ budget≤1/2) (width : RatInput.Encoder.fieldSize budget≤B)
    (room : history.length≤B) (archive : records.sum≤B) (original : arithmeticScale input C budget≤B) :
    ∀ call∈(candidate input available budget limit history records).words,
      (wordInput (input.experiment call.stage) call.target call.word).length+call.word.1+1≤100000*(B+1)^2 := by
  unfold candidate
  dsimp only
  cases finished:(replay input available budget records history).result with
  | none => intro call member;cases member
  | some cache =>
      have bounded:=replay_cacheBound input available budget records history cache finished
      intro call member
      have source:=decision_word_origin input limit history cache (kernel budget records cache) call member
      have target:=kernel_target_width budget records cache B valid width (bounded.2.2.trans room) archive call.target source.1
      have material:=RootPaper.Prep.experiment_material_le_input I input C budget call.stage
      have scale:=RootPaper.Prep.original_bits_le_scale I input C budget
      have alphabet:=((RootB23.PrepScalar.each_alphabet_le_total I input call.stage).trans
        (RootB23.PrepScalar.alphabet_total_le_scale I input C budget)).trans original
      exact word_input_size _ _ _ B (material.trans (scale.trans original)) target alphabet
        (source.2.trans (bounded.1.trans room))

def preparedCandidate (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0<budget) (history : List (VisibleEvent I)) (records : List Nat) : Computation input :=
  candidate input available budget
    (some (RootPaper.B23.preparedQuotas (RootPaper.Prep.preparationCalculation input C budget positive).value)) history records

theorem preparedCandidate_eq (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0<budget) (history : List (VisibleEvent I)) (records : List Nat) :
    preparedCandidate input C available budget positive history records=
      candidate input available budget (some (computedQuotas input budget)) history records := by
  unfold preparedCandidate
  rw [RootPaper.B23.preparedQuotas_eq]

theorem quota_le_scale (input : StatisticalInput I) (C : Contract I) (budget : Rat) (stage : I.Stage) :
    computedQuotas input budget stage≤arithmeticScale input C budget := by
  have one:computedQuotas input budget stage≤numericalQuota input budget:=
    Finset.single_le_sum (fun i _=>Nat.zero_le (computedQuotas input budget i)) (Finset.mem_univ stage)
  unfold arithmeticScale
  omega

theorem budget_le_scale (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    RatInput.Encoder.fieldSize budget≤arithmeticScale input C budget :=
  RootPaper.Prep.input_rat_field I input C budget budget (by
    simp only [RootPaper.Prep.originalData,List.mem_append,List.mem_singleton]
    tauto)

noncomputable def localRate (runtime : WordCode) : Nat:=256*513*runningRate runtime

theorem local_fee_bound (runtime : WordCode) (input : StatisticalInput I) (C : Contract I)
    (available : Finset I.Tool) (budget : Rat) (positive : 0<budget) (small : budget≤1/2)
    (history : List (VisibleEvent I)) (records : List Nat) (bits : Nat) :
    let B:=localSize input C budget history records bits
    256*bitCost runtime B bits records (preparedCandidate input C available budget positive history records)≤
      localRate runtime*(B+1)^(runningDegree runtime+2) := by
  dsimp only
  let B:=localSize input C budget history records bits
  have original : arithmeticScale input C budget≤B:=by unfold B localSize;omega
  have room:history.length≤B:=by unfold B localSize;omega
  have archive:records.sum≤B:=by unfold B localSize;omega
  have recordLength:records.length≤B:=by unfold B localSize;omega
  have wordWidth:bits≤B:=by unfold B localSize;omega
  have width:RatInput.Encoder.fieldSize budget≤B:=(budget_le_scale input C budget).trans original
  have material:instanceMaterial input≤B:=(instance_material_input input C budget).trans original
  have stages:I.stageCount≤B:=by unfold B localSize arithmeticScale inputSize;omega
  have tools:I.toolCount≤B:=by unfold B localSize arithmeticScale inputSize;omega
  have histMaterial:historyMaterial history≤B:=by unfold B localSize;omega
  have fields:HistoryFieldBits B history:=fun event present n member=>
    (history_material_fields history event present n member).trans histMaterial
  have alphabets:∀ stage,(input.experiment stage).alphabetSize≤B:=fun stage=>
    ((RootB23.PrepScalar.each_alphabet_le_total I input stage).trans
      (RootB23.PrepScalar.alphabet_total_le_scale I input C budget)).trans original
  rw [preparedCandidate_eq]
  have calls:=candidate_calls input available budget (some (computedQuotas input budget)) history records B ⟨positive,small⟩ width room archive
  have control:=candidate_control input available budget (computedQuotas input budget) history records B ⟨positive,small⟩ width room fields stages tools material alphabets
    (fun stage=>(quota_le_scale input C budget stage).trans original)
  have words:=candidate_words input C available budget (some (computedQuotas input budget)) history records B ⟨positive,small⟩ width room archive original
  have all:=aggregate_bound runtime B bits records _ calls control recordLength wordWidth words
  have units:=candidate_units input available budget (some (computedQuotas input budget)) history records
  have larger:=Nat.mul_le_mul_left 512 (Nat.pow_le_pow_left (Nat.add_le_add_right room 1) 2)
  have one:1≤(B+1)^2:=Nat.one_le_pow _ _ (by omega)
  have upper : (candidate input available budget (some (computedQuotas input budget)) history records).units+1≤513*(B+1)^2 := by omega
  have scaled:=Nat.mul_le_mul_right ((B+1)^runningDegree runtime) (Nat.mul_le_mul_right (runningRate runtime) upper)
  have result:=Nat.mul_le_mul_left 256 (all.trans scaled)
  exact result.trans_eq (by unfold localRate;rw [pow_add];ring)

end RootPaper.TableCost
