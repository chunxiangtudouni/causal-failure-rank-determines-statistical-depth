module

public import PaperProofs.Retained.PRet_DelayedPolicy_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetActionOrigins019

open Common Common.Native PRetDelayedPolicy010

variable {I : Instance}

theorem catchUp_review (history : List (VisibleEvent I)) (destination : ℕ)
    (next : Action I) (stage : I.Stage)
    (h : catchUp history destination next = .review stage) : next = .review stage := by
  unfold catchUp at h
  split_ifs at h
  exact h

theorem catchUp_write (history : List (VisibleEvent I)) (destination : ℕ)
    (next : Action I) (stage : I.Stage) (bit : Bool)
    (h : catchUp history destination next = .write stage bit) : next = .write stage bit := by
  unfold catchUp at h
  split_ifs at h
  exact h

theorem catchUp_execute (history : List (VisibleEvent I)) (destination : ℕ)
    (next : Action I) (handle : MismatchHandle I) (tool : I.Tool)
    (h : catchUp history destination next = .execute handle tool) : next = .execute handle tool := by
  unfold catchUp at h
  split_ifs at h
  exact h

theorem paymentAction_not_review (source : Startup I) (history : List (VisibleEvent I))
    (stage : I.Stage) : paymentAction source history ≠ .review stage := by
  unfold paymentAction
  split <;> try { intro h; cases h }
  split <;> try { intro h; cases h }
  split_ifs <;> intro h <;> cases h

theorem paymentAction_not_write (source : Startup I) (history : List (VisibleEvent I))
    (stage : I.Stage) (bit : Bool) : paymentAction source history ≠ .write stage bit := by
  unfold paymentAction
  split <;> try { intro h; cases h }
  split <;> try { intro h; cases h }
  split_ifs <;> intro h <;> cases h

theorem candidate_review (source : Startup I) (sourceAction : Action I)
    (history : List (VisibleEvent I)) (stage : I.Stage)
    (h : candidate source sourceAction history = .review stage) :
    source.halted = false ∧ sourceAction = .review stage := by
  unfold candidate at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact False.elim (paymentAction_not_review source history stage (catchUp_review history _ _ stage h))
      · cases h
  · rename_i hhalt
    refine ⟨Bool.eq_false_iff.mpr hhalt, ?_⟩
    cases sourceAction <;> try { cases h }
    all_goals
      have hn := catchUp_review history _ _ stage h
      exact hn

theorem candidate_write (source : Startup I) (sourceAction : Action I)
    (history : List (VisibleEvent I)) (stage : I.Stage) (bit : Bool)
    (h : candidate source sourceAction history = .write stage bit) :
    source.halted = false ∧ sourceAction = .write stage bit := by
  unfold candidate at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact False.elim (paymentAction_not_write source history stage bit (catchUp_write history _ _ stage bit h))
      · cases h
  · rename_i hhalt
    refine ⟨Bool.eq_false_iff.mpr hhalt, ?_⟩
    cases sourceAction <;> try { cases h }
    all_goals
      have hn := catchUp_write history _ _ stage bit h
      exact hn

theorem guarded_eq_raw {Seed : Type*} (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (seed : Seed) (history : List (VisibleEvent I))
    (action : Action I) (hne : action ≠ .abandon)
    (h : rule accounting source seed history = action) :
    raw accounting source seed history = action := by
  unfold rule PRetRetainedGuard007.guarded at h
  split_ifs at h
  · exact h
  · exact False.elim (hne h.symm)

theorem paymentAction_execute (source : Startup I) (history : List (VisibleEvent I))
    (handle : MismatchHandle I) (tool : I.Tool)
    (h : paymentAction source history = .execute handle tool) :
    ∃ execution, source.executions[(historyExecutions history).length]? = some execution ∧
      execution.handle.stage = handle.stage ∧ execution.tool = tool := by
  unfold paymentAction at h
  split at h
  · cases h
  · rename_i execution hexecution
    split at h
    · cases h
    · split at h
      · cases h
        exact ⟨execution, hexecution, rfl, rfl⟩
      · cases h

theorem candidate_execute (source : Startup I) (sourceAction : Action I)
    (history : List (VisibleEvent I)) (handle : MismatchHandle I) (tool : I.Tool)
    (h : candidate source sourceAction history = .execute handle tool) :
    ∃ execution, source.executions[(historyExecutions history).length]? = some execution ∧
      execution.handle.stage = handle.stage ∧ execution.tool = tool := by
  unfold candidate at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact paymentAction_execute source history handle tool (catchUp_execute history _ _ handle tool h)
      · cases h
  · cases sourceAction <;> try { cases h }
    all_goals
      have hn := catchUp_execute history _ _ handle tool h
      cases hn

end PaperProofs.Retained.PRetActionOrigins019
