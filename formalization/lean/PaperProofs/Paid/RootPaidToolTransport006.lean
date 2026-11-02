module

public import PaperProofs.Paid.RootPaidToolTransport005

@[expose] public section

namespace RootPaidToolTransport

open MeasureTheory PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem up_down_handle (n k : ℕ) (handle : MismatchHandle (freshInstance n (k + 1))) :
    upHandle n k (downHandle n k handle) = handle := by
  cases handle
  rfl

theorem upHandle_injective (n k : ℕ) : Function.Injective (upHandle n k) := by
  intro a b h
  exact (down_up_handle n k a).symm.trans ((congrArg (downHandle n k) h).trans (down_up_handle n k b))

def downAction (n k : ℕ) : Action (freshInstance n (k + 1)) → Action (freshInstance n k)
  | .review stage => .review (downStage n k stage)
  | .write stage bit => .write (downStage n k stage) bit
  | .allocate handle tool => (downTool k tool).elim .abandon (fun small => .allocate (downHandle n k handle) small)
  | .execute handle tool => (downTool k tool).elim .abandon (fun small => .execute (downHandle n k handle) small)
  | .advance stage => .advance (downStage n k stage)
  | .stop => .stop
  | .abandon => .abandon

theorem down_up_action (n k : ℕ) (action : Action (freshInstance n k)) :
    downAction n k (upAction n k action) = action := by
  cases action with
  | review _ => rfl
  | write _ _ => rfl
  | allocate handle tool =>
    exact congrArg (fun option : Option (Fin k) => option.elim (.abandon : Action (freshInstance n k))
      (fun small => .allocate handle small)) (down_up_tool k tool)
  | execute handle tool =>
    exact congrArg (fun option : Option (Fin k) => option.elim (.abandon : Action (freshInstance n k))
      (fun small => .execute handle small)) (down_up_tool k tool)
  | advance _ => rfl
  | stop => rfl
  | abandon => rfl

theorem reflectStep (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (tapes : ReviewTapes (P.freshInput n k fee hfee))
    {s : State (freshInstance n k)} {next : State (freshInstance n (k + 1))}
    {action : Action (freshInstance n (k + 1))}
    (hs : Step (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (upTapes P fee hfee n k tapes) (upState n k s) action next)
    (halloc : ∀ handle tool, action = .allocate handle tool → tool ∈ upImage k) :
    ∃ (smallAction : Action (freshInstance n k)) (smallNext : State (freshInstance n k)),
      upAction n k smallAction = action ∧
      Step (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
        tapes s smallAction smallNext ∧ upState n k smallNext = next := by
  have finish (smallAction : Action (freshInstance n k)) (smallNext : State (freshInstance n k))
      (ha : upAction n k smallAction = action)
      (hsmall : Step (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
        tapes s smallAction smallNext) :
      ∃ (smallAction : Action (freshInstance n k)) (smallNext : State (freshInstance n k)),
        upAction n k smallAction = action ∧
        Step (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
          tapes s smallAction smallNext ∧ upState n k smallNext = next := by
    refine ⟨smallAction, smallNext, ha, hsmall, ?_⟩
    exact step_deterministic _ _ _ _ _ (ha ▸ upStep P fee hfee n k tapes hsmall) hs
  cases hs with
  | review stage live port _ =>
    exact finish (.review (downStage n k stage)) _
      (congrArg Action.review (up_down_stage n k stage))
      (.review s _ live port (.inl rfl))
  | write stage bit live port _ =>
    exact finish (.write (downStage n k stage) bit) _
      (congrArg (fun current => Action.write current bit) (up_down_stage n k stage))
      (.write s _ bit live port (.inl rfl))
  | allocate handle tool active valid _compatible unused unallocated window _ =>
    obtain ⟨smallTool, _, rfl⟩ := Finset.mem_image.mp (halloc handle tool rfl)
    have hu : ∀ a ∈ s.ledger.commitments, a.tool ≠ smallTool := by
      intro a ha heq
      apply unused (upCommitment n k a) (List.mem_map.mpr ⟨a, ha, rfl⟩)
      exact congrArg (upTool k) heq
    have hh : ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ (downHandle n k handle).stage := by
      intro a ha heq
      apply unallocated (upCommitment n k a) (List.mem_map.mpr ⟨a, ha, rfl⟩)
      exact (congrArg (upStage n k) heq).trans (up_down_stage n k handle.stage)
    have hm : smallTool ∈ (freshInstance n k).eligible (downHandle n k handle).stage := by
      simp [freshInstance, Instance.eligible]
      exact Finset.mem_univ _
    exact finish (.allocate (downHandle n k handle) smallTool) _
      (congrArg (fun h : MismatchHandle (freshInstance n (k + 1)) =>
        Action.allocate h (upTool k smallTool)) (up_down_handle n k handle))
      (.allocate s _ smallTool active valid hm hu hh window (.inl rfl))
  | execute handle tool active valid _compatible committed unused uncorrected window _ =>
    obtain ⟨bigCommit, hbigCommit, hhandle, htool⟩ := committed
    change bigCommit ∈ s.ledger.commitments.map (upCommitment n k) at hbigCommit
    obtain ⟨commit, hcommit, rfl⟩ := List.mem_map.mp hbigCommit
    have hc : ∃ a ∈ s.ledger.commitments, a.handle = downHandle n k handle ∧ a.tool = commit.tool := by
      exact ⟨commit, hcommit, congrArg (downHandle n k) hhandle, rfl⟩
    have hu : ∀ e ∈ s.ledger.executions, e.tool ≠ commit.tool := by
      intro e he heq
      apply unused (upExecution n k e) (List.mem_map.mpr ⟨e, he, rfl⟩)
      exact (congrArg (upTool k) heq).trans htool
    have hh : ∀ e ∈ s.ledger.executions, e.handle.stage ≠ (downHandle n k handle).stage := by
      intro e he heq
      apply uncorrected (upExecution n k e) (List.mem_map.mpr ⟨e, he, rfl⟩)
      exact (congrArg (upStage n k) heq).trans (up_down_stage n k handle.stage)
    have hm : commit.tool ∈ (freshInstance n k).eligible (downHandle n k handle).stage := by
      simp [freshInstance, Instance.eligible]
      exact Finset.mem_univ _
    exact finish (.execute (downHandle n k handle) commit.tool) _
      (congrArg₂ Action.execute (up_down_handle n k handle) htool)
      (.execute s _ commit.tool active valid hm hc hu hh window (.inl rfl))
  | advance stage live written _ =>
    exact finish (.advance (downStage n k stage)) _
      (congrArg Action.advance (up_down_stage n k stage))
      (.advance s _ live written (.inl rfl))
  | stop active => exact finish .stop _ rfl (.stop s active)
  | abandon active => exact finish .abandon _ rfl (.abandon s active)

theorem upLedger_success_reverse (n k : ℕ) (L : Ledger (freshInstance n k))
    (h : (upLedger n k L).success (paidRelaxedContract _)) :
    L.success (paidRelaxedContract _) := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro stage time ht hw
    obtain ⟨ha, he⟩ := h.2.2.1 (upStage n k stage) time ht hw
    constructor
    · intro hc
      obtain ⟨a, hamem, hastage, hatime⟩ := ha hc
      change a ∈ L.commitments.map (upCommitment n k) at hamem
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hamem
      exact ⟨b, hb, upStage_injective n k hastage, hatime⟩
    · intro hc
      obtain ⟨e, hemem, hestage, hetime⟩ := he hc
      change e ∈ L.executions.map (upExecution n k) at hemem
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hemem
      exact ⟨b, hb, upStage_injective n k hestage, hetime⟩
  · intro stage
    rcases h.2.2.2 (upStage n k stage) with hw | ⟨e, he, hstage⟩
    · exact Or.inl hw
    · change e ∈ L.executions.map (upExecution n k) at he
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      exact Or.inr ⟨b, hb, upStage_injective n k hstage⟩

end RootPaidToolTransport
