module
public import PaperProofs.Common.BoundedNormalIO

/-! All-path data bounds used by the reference work count. No successful-path
conditioning or computational cost premise is added to the native policy. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
variable {I : Instance}

def CacheBound (limit : Nat) (cache : ReferenceReplayCache I) : Prop :=
  cache.seen.length≤limit ∧ cache.entryHistory.length≤limit ∧ cache.events.length≤limit

private theorem some_branch {α : Type*} (test : Prop) [Decidable test] (value : α) (next : α)
    (actual : (if test then some value else none)=some next) : test ∧ value=next := by
  by_cases guard : test
  · rw [ite_eq_left guard] at actual
    exact ⟨guard,Option.some.inj actual⟩
  · rw [ite_eq_right guard] at actual
    cases actual

theorem step_cacheBound (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (cache next : ReferenceReplayCache I) (event : VisibleEvent I) (limit : Nat)
    (bounded : CacheBound limit cache)
    (actual : referenceAvailableStep input available budget cache event=some next) : CacheBound (limit+1) next := by
  cases halted : cache.halted with
  | true => simp only [referenceAvailableStep,halted,ite_true] at actual;cases actual
  | false =>
      cases event with
      | observation stage symbol =>
          simp only [referenceAvailableStep,halted,Bool.false_eq_true,ite_false] at actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,same⟩:=some_branch _ _ _ actual
          subst next
          simp only [CacheBound,List.length_append,List.length_cons,List.length_nil] at *
          omega
      | wrote stage bit serial =>
          simp only [referenceAvailableStep,halted,Bool.false_eq_true,ite_false] at actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,same⟩:=some_branch _ _ _ actual
          subst next
          simp only [CacheBound,List.length_append,List.length_cons,List.length_nil] at *
          omega
      | report stage truth serial =>
          simp only [referenceAvailableStep,halted,Bool.false_eq_true,ite_false] at actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,same⟩:=some_branch _ _ _ actual
          subst next
          simp only [CacheBound,List.length_append,List.length_cons,List.length_nil] at *
          omega
      | committed handle tool =>
          simp only [referenceAvailableStep,halted,Bool.false_eq_true,ite_false] at actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,same⟩:=some_branch _ _ _ actual
          subst next
          simp only [CacheBound,List.length_append,List.length_cons,List.length_nil] at *
          omega
      | executed handle tool =>
          simp only [referenceAvailableStep,halted,Bool.false_eq_true,ite_false] at actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,same⟩:=some_branch _ _ _ actual
          subst next
          simp only [CacheBound,List.length_append,List.length_cons,List.length_nil] at *
          omega
      | advanced stage =>
          simp only [referenceAvailableStep,halted,Bool.false_eq_true,ite_false] at actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,_,actual⟩:=Option.bind_eq_some_iff.mp actual
          obtain ⟨_,same⟩:=some_branch _ _ _ actual
          subst next
          simp only [CacheBound,List.length_append,List.length_cons,List.length_nil] at *
          omega
      | stopped =>
          simp only [referenceAvailableStep,halted,Bool.false_eq_true,ite_false] at actual
          obtain ⟨_,same⟩:=some_branch _ _ _ actual
          subst next
          simp only [CacheBound,List.length_append,List.length_cons,List.length_nil] at *
          omega
      | abandoned =>
          simp only [referenceAvailableStep,halted,Bool.false_eq_true,ite_false] at actual
          obtain ⟨_,same⟩:=some_branch _ _ _ actual
          subst next
          simp only [CacheBound,List.length_append,List.length_cons,List.length_nil] at *
          omega

theorem initial_cacheBound : CacheBound 0 (referenceReplayInitial I) := by
  simp [CacheBound,referenceReplayInitial]

theorem prefix_history_length (input : StatisticalInput I) (C : Contract I)
    (early : C.reporting=.early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage→Bool)
    (tapes : ReviewTapes input) {n : Nat} {state : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n state) : state.history.length≤2*n := by
  induction hp with
  | initial => simp [initial]
  | @next n before after earlier move ih =>
      generalize selected : policy seed before.history=action at move
      cases move <;> simp only [record,stopState,List.length_append,List.length_cons,List.length_nil,
        writeResponses,early,ite_true] <;> omega

theorem run_history_length (input : StatisticalInput I) (C : Contract I)
    (early : C.reporting=.early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} [MeasurableSpace Seed] (policy : Policy input C mode accounting Seed)
    (sample : Seed×input.World) (clock : Nat) :
    (run input C mode accounting policy.rule sample clock).history.length≤2*clock := by
  obtain ⟨n,before,hp⟩:=run_has_prefix input C mode accounting policy.rule policy.legal sample clock
  exact (prefix_history_length input C early mode accounting policy.rule sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) hp).trans (Nat.mul_le_mul_left 2 before)

end RootPaper.Reference
