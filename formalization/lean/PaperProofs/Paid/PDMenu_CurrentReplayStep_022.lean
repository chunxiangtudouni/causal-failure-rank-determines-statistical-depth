module

public import PaperProofs.Paid.PDMenu_CurrentHeadKernel_006
public import PaperProofs.Common.HistorySuffixFullRun
public import PaperProofs.Common.NativeContracts

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*}

theorem paidHistorySuffixStep (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (hcurrent : C.allocation = .currentWindow)
    (hpayment : C.execution = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (sourceTapes : ReviewTapes input)
    (targetTapes : ReviewTapes (input.freshSuffix first))
    {Seed : Type*} (targetRule : PolicyRule (I.freshSuffix first) Seed) (seed : Seed)
    (targetTruth : (I.freshSuffix first).Stage → Bool)
    {n : ℕ} {source sourceNext : State I} {target : State (I.freshSuffix first)}
    (hp : Prefix (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule seed targetTruth targetTapes n target)
    (view : HistorySuffixStateView input first source target)
    {action : Action I} {targetAction : Action (I.freshSuffix first)}
    (haction : suffixActionOf first target.history action = some targetAction)
    (hs : Step input C mode accounting sourceTapes source action sourceNext) :
    ∃ targetNext, Step (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetTapes target targetAction targetNext := by
  have hactive (ha : source.halted = false) : target.halted = false := view.halted.symm.trans ha
  have hlive (stage : I.Stage) (hf : first ≤ stage.val) (hl : liveStage source stage) :
      liveStage target (suffixStageOf first stage hf) := by
    refine ⟨hactive hl.1, ?_⟩
    have hc := view.cursor
    have hs : source.cursor = stage.val := hl.2
    change target.cursor = stage.val - first
    omega
  have hvalid (handle : MismatchHandle I) (hf : first ≤ handle.stage.val)
      (hv : validHandle source handle) : validHandle target (suffixHandleOf first target.history handle hf) :=
    suffixHandleOf_valid_of_prefix input first _ .uncapped _ targetRule seed targetTruth targetTapes hp
      source handle hf hv (view.written handle.stage hf) (view.truth handle.stage hf)
      (view.reported handle.stage hf hv.2.2)
  have hcompatible (stage : I.Stage) (hf : first ≤ stage.val) (tool : I.Tool)
      (hm : tool ∈ I.eligible stage) : tool ∈ (I.freshSuffix first).eligible (suffixStageOf first stage hf) := by
    rw [I.freshSuffix_eligible, freshStageLift_suffixStageOf]
    exact hm
  cases hs with
  | review stage live port resources =>
    simp only [suffixActionOf] at haction
    split at haction
    next hf =>
      cases haction
      exact ⟨_, .review target _ (hlive stage hf live) ((view.written stage hf).trans port) (.inl rfl)⟩
    next hf => cases haction
  | write stage bit live port resources =>
    simp only [suffixActionOf] at haction
    split at haction
    next hf =>
      cases haction
      exact ⟨_, .write target _ bit (hlive stage hf live) ((view.written stage hf).trans port) (.inl rfl)⟩
    next hf => cases haction
  | allocate handle tool active valid compatible unused unallocated window resources =>
    simp only [suffixActionOf] at haction
    split at haction
    next hf =>
      cases haction
      have hu : ∀ b ∈ target.ledger.commitments, b.tool ≠ tool := by
        intro b hb heq
        obtain ⟨a, ha, _, ht⟩ := view.commitments_reverse b hb
        exact unused a ha (ht.trans heq)
      have hs : ∀ b ∈ target.ledger.commitments,
          b.handle.stage ≠ (suffixHandleOf first target.history handle hf).stage := by
        intro b hb heq
        obtain ⟨a, ha, hstage, _⟩ := view.commitments_reverse b hb
        apply unallocated a ha
        rw [hstage, heq]
        exact freshStageLift_suffixStageOf first handle.stage hf
      refine ⟨_, .allocate target _ tool (hactive active) (hvalid handle hf valid)
        (hcompatible handle.stage hf tool compatible) hu hs ?_ (.inl rfl)⟩
      intro _
      have hsource : source.cursor = handle.stage.val := window hcurrent
      have hc := view.cursor
      change target.cursor = handle.stage.val - first
      omega
    next hf => cases haction
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    simp only [suffixActionOf] at haction
    split at haction
    next hf =>
      cases haction
      have hc : ∃ b ∈ target.ledger.commitments,
          b.handle = suffixHandleOf first target.history handle hf ∧ b.tool = tool := by
        obtain ⟨a, ha, hh, ht⟩ := committed
        obtain ⟨b, hb, bh, bt⟩ := view.commitments_forward a ha (by simpa only [hh] using hf)
        exact ⟨b, hb, by simpa only [hh] using bh, bt.trans ht⟩
      have hu : ∀ b ∈ target.ledger.executions, b.tool ≠ tool := by
        intro b hb heq
        obtain ⟨a, ha, _, ht⟩ := view.executions_reverse b hb
        exact unused a ha (ht.trans heq)
      have hs : ∀ b ∈ target.ledger.executions,
          b.handle.stage ≠ (suffixHandleOf first target.history handle hf).stage := by
        intro b hb heq
        obtain ⟨a, ha, hstage, _⟩ := view.executions_reverse b hb
        apply uncorrected a ha
        rw [hstage, heq]
        exact freshStageLift_suffixStageOf first handle.stage hf
      refine ⟨_, .execute target _ tool (hactive active) (hvalid handle hf valid)
        (hcompatible handle.stage hf tool compatible) hc hu hs ?_ (.inl rfl)⟩
      intro _
      have hsource : source.cursor = handle.stage.val := window hpayment
      have hcursor := view.cursor
      change target.cursor = handle.stage.val - first
      omega
    next hf => cases haction
  | advance stage live written resources =>
    simp only [suffixActionOf] at haction
    split at haction
    next hf =>
      cases haction
      exact ⟨_, .advance target _ (hlive stage hf live)
        (by rw [view.written stage hf]; exact written) (.inl rfl)⟩
    next hf => cases haction
  | stop active => cases haction; exact ⟨_, .stop target (hactive active)⟩
  | abandon active => cases haction; exact ⟨_, .abandon target (hactive active)⟩


end PDMenu
