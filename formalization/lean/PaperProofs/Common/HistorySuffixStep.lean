module

public import PaperProofs.Common.HistorySuffixReplay
import Lean.Elab.Tactic.Omega

/-!
Ledger projection needed in the B09 replay induction. These are ordinary
cursor/ledger relations, not a legal-target-step or cost/risk conclusion.
-/

@[expose] public section

namespace PaperProofs.Common.Native

variable {I : Instance}

structure HistorySuffixStateView (input : StatisticalInput I) (first : ℕ)
    (source : State I) (target : State (I.freshSuffix first)) : Prop where
  cursor : source.cursor = first + target.cursor
  halted : source.halted = target.halted
  truth : ∀ stage (hf : first ≤ stage.val),
    target.ledger.truth (suffixStageOf first stage hf) = source.ledger.truth stage
  written : ∀ stage (hf : first ≤ stage.val),
    target.ledger.written (suffixStageOf first stage hf) = source.ledger.written stage
  reviews : ∀ stage (hf : first ≤ stage.val),
    target.ledger.reviews (suffixStageOf first stage hf) = source.ledger.reviews stage
  reported : ∀ stage (hf : first ≤ stage.val),
    (∃ t, source.ledger.reportTime stage = some t) →
      ∃ t, target.ledger.reportTime (suffixStageOf first stage hf) = some t
  commitments_forward : ∀ a ∈ source.ledger.commitments,
    ∀ hf : first ≤ a.handle.stage.val, ∃ b ∈ target.ledger.commitments,
      b.handle = suffixHandleOf first target.history a.handle hf ∧ b.tool = a.tool
  commitments_reverse : ∀ b ∈ target.ledger.commitments,
    ∃ a ∈ source.ledger.commitments,
      a.handle.stage = I.freshStageLift first b.handle.stage ∧ a.tool = b.tool
  executions_reverse : ∀ b ∈ target.ledger.executions,
    ∃ a ∈ source.ledger.executions,
      a.handle.stage = I.freshStageLift first b.handle.stage ∧ a.tool = b.tool

/-- A source action past the saved entry is legal as a genuine fresh native
step once the elementary ledger projection has been established. Delayed
executions retain their commitment, tool and stage guards. -/
theorem HistorySuffixStateView.step (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (hcurrent : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (sourceTapes : ReviewTapes input)
    (targetTapes : ReviewTapes (input.freshSuffix first))
    {Seed : Type*} (targetRule : PolicyRule (I.freshSuffix first) Seed) (seed : Seed)
    (targetTruth : (I.freshSuffix first).Stage → Bool)
    {n : ℕ} {source sourceNext : State I} {target : State (I.freshSuffix first)}
    (hp : Prefix (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule seed targetTruth targetTapes n target)
    (view : HistorySuffixStateView input first source target)
    {action : Action I} {targetAction : Action (I.freshSuffix first)}
    (haction : suffixActionOf first target.history action = some targetAction)
    (hs : Step input C mode accounting sourceTapes source action sourceNext) :
    ∃ targetNext, Step (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
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
      intro hcurrent
      cases hcurrent
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

/-- Every genuine early mismatch handle passes the public replay test. -/
theorem replayValidHandle_complete (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (handle : MismatchHandle I) (hvalid : validHandle s handle) : replayValidHandle s.history handle := by
  obtain ⟨hw, hs, time, ht⟩ := hvalid
  unfold replayValidHandle
  rw [prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp handle.stage, ht]
  simp only [Option.map_some]
  rw [prefix_historyWritten input C mode accounting rule seed truth tapes hp handle.stage,
    prefix_historyWriteSerial input C mode accounting rule seed truth tapes hp handle.stage]
  exact ⟨hw, hs, hs.symm⟩

/-- Completeness of the public guard on real prefixes. Allocation membership
is the sole additional condition: it records the fixed saved available set.
The execute clause has no cursor restriction. -/
theorem replayAllowsAction_complete (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s next : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (available : Finset I.Tool) {action : Action I}
    (hs : Step input C mode accounting tapes s action next)
    (havailable : ∀ handle tool, action = .allocate handle tool → tool ∈ available) :
    replayAllowsAction available s.history action := by
  cases hs with
  | review stage live port resources =>
    change historyCursor s.history = stage.val ∧ historyWritten s.history stage = none
    rw [prefix_historyCursor input C mode accounting rule seed truth tapes hp,
      prefix_historyWritten input C mode accounting rule seed truth tapes hp stage]
    exact ⟨live.2, port⟩
  | write stage bit live port resources =>
    change historyCursor s.history = stage.val ∧ historyWritten s.history stage = none
    rw [prefix_historyCursor input C mode accounting rule seed truth tapes hp,
      prefix_historyWritten input C mode accounting rule seed truth tapes hp stage]
    exact ⟨live.2, port⟩
  | allocate handle tool active valid compatible unused unallocated window resources =>
    refine ⟨havailable handle tool rfl, ?_,
      replayValidHandle_complete input C hearly mode accounting rule seed truth tapes hp handle valid,
      compatible, ?_, ?_⟩
    · rw [prefix_historyCursor input C mode accounting rule seed truth tapes hp]
      exact window hcurrent
    · apply (prefix_historyUnused_iff input C mode accounting rule seed truth tapes hp tool).mpr
      exact unused
    · intro pair hm
      rw [prefix_historyCommitments input C mode accounting rule seed truth tapes hp] at hm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact unallocated a ha
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    refine ⟨replayValidHandle_complete input C hearly mode accounting rule seed truth tapes hp handle valid,
      compatible, ?_, ?_, ?_⟩
    · rw [prefix_historyCommitments input C mode accounting rule seed truth tapes hp]
      obtain ⟨a, ha, hh, ht⟩ := committed
      exact List.mem_map.mpr ⟨a, ha, by rw [hh, ht]⟩
    · intro pair hm
      rw [prefix_historyExecutions input C mode accounting rule seed truth tapes hp] at hm
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      exact unused e he
    · intro pair hm
      rw [prefix_historyExecutions input C mode accounting rule seed truth tapes hp] at hm
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      exact uncorrected e he
  | advance stage live written resources =>
    change historyCursor s.history = stage.val ∧ historyWritten s.history stage ≠ none
    rw [prefix_historyCursor input C mode accounting rule seed truth tapes hp,
      prefix_historyWritten input C mode accounting rule seed truth tapes hp stage]
    exact ⟨live.2, written⟩
  | stop active => exact True.intro
  | abandon active => exact True.intro

/-- On a real legal available-tool action the implemented guard makes no
change, including when the action executes an earlier suffix commitment. -/
theorem guardedReplayRule_eq_of_step (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule raw : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s next : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (available : Finset I.Tool)
    (hs : Step input C mode accounting tapes s (raw seed s.history) next)
    (havailable : ∀ handle tool, raw seed s.history = .allocate handle tool → tool ∈ available) :
    guardedReplayRule available raw seed s.history = raw seed s.history := by
  have ha := replayAllowsAction_complete input C hearly hcurrent mode accounting rule seed truth tapes hp available hs havailable
  simp only [guardedReplayRule, ha, ↓reduceIte]

end PaperProofs.Common.Native
