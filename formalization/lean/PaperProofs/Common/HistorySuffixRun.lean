module

public import PaperProofs.Common.HistorySuffixStep
public import PaperProofs.Common.HistorySuffixTransport
import Lean.Elab.Tactic.Omega

/-!
B09 real-entry initialization and preservation of the actual replay run view.
No run alignment or desired cost/risk inequality is an input to entry facts.
-/

@[expose] public section

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

/-- A first cursor entry is active and every as-yet-unborn review/write port
is untouched. This follows from actual steps, including arbitrary spending,
stops and delayed executions before the entry. -/
theorem firstEntryAt_unborn (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first n : ℕ) (hentry : FirstEntryAt input C mode accounting rule first n sample) :
    (run input C mode accounting rule sample n).halted = false ∧
      ∀ stage : I.Stage, first ≤ stage.val →
        (run input C mode accounting rule sample n).ledger.written stage = none ∧
          (run input C mode accounting rule sample n).ledger.reviews stage = 0 := by
  cases n with
  | zero => exact ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  | succ n =>
    have hne := hentry.2 n (Nat.lt_succ_self n)
    have hcursor := hentry.1
    obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample n
    by_cases hh : (run input C mode accounting rule sample n).halted = true
    · rw [run_succ_of_halted input C mode accounting rule sample n hh] at hcursor
      exact (hne hcursor).elim
    · have ha : (run input C mode accounting rule sample n).halted = false := Bool.eq_false_iff.mpr hh
      obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
      have hr := run_succ_of_step input C mode accounting rule sample n next ha hs
      rw [hr] at hcursor ⊢
      have hinv := prefix_cursorInvariant input C mode accounting rule sample.1 _ _ hp
      generalize rule sample.1 (run input C mode accounting rule sample n).history = action at hs
      cases hs <;> try exact (hne hcursor).elim
      case advance stage live written resources =>
        refine ⟨rfl, ?_⟩
        intro future hf
        have hb : (run input C mode accounting rule sample n).cursor < future.val := by
          change (run input C mode accounting rule sample n).cursor + 1 = first at hcursor
          omega
        exact ⟨hinv.future_written future hb, hinv.future_reviews future hb⟩

/-- The genuine entry state, with the same restricted hidden world, provides
the initial ledger view against the completely fresh target system. The
relation is concluded from the actual entry, not assumed as an alignment. -/
theorem historySuffixStateView_firstEntry (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first n : ℕ) (hentry : FirstEntryAt input C mode accounting rule first n sample) :
    HistorySuffixStateView input first (run input C mode accounting rule sample n)
      (initial ((input.freshSuffix first).truthAt (input.restrictFreshWorld first sample.2))) := by
  obtain ⟨ha, hfuture⟩ := firstEntryAt_unborn input C mode accounting rule hlegal sample first n hentry
  obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample n
  have hinv := prefix_invariant input C mode accounting rule sample.1 _ _ hp
  have htruth := prefix_truth input C mode accounting rule sample.1 _ _ hp
  constructor
  · simpa only [initial, Nat.add_zero] using hentry.1
  · exact ha
  · intro stage hf
    change (input.freshSuffix first).truthAt (input.restrictFreshWorld first sample.2)
        (suffixStageOf first stage hf) = _
    rw [restrictFreshWorld_truth, freshStageLift_suffixStageOf, htruth]
  · intro stage hf
    exact (hfuture stage hf).1.symm
  · intro stage hf
    exact (hfuture stage hf).2.symm
  · intro stage hf ⟨time, ht⟩
    exact (hinv.report_written stage time ht (hfuture stage hf).1).elim
  · intro a ha hf
    have hg := (hinv.commitment_genuine a ha).1
    rw [(hfuture a.handle.stage hf).1] at hg
    cases hg
  · intro b hb
    cases hb
  · intro b hb
    cases hb

/-- One genuine old execution leaves every future ledger projection intact;
its source execution and accounting entries remain present in the source. -/
theorem HistorySuffixStateView.executeOld (input : StatisticalInput I) (first : ℕ)
    (accounting : NormalAccounting I) {source : State I} {target : State (I.freshSuffix first)}
    (view : HistorySuffixStateView input first source target)
    (handle : MismatchHandle I) (tool : I.Tool) (_hold : handle.stage.val < first)
    (hactive : source.halted = false) :
    HistorySuffixStateView input first
      (record accounting source (.execute handle tool) [.executed handle tool]
        (executeLedger source handle tool) source.cursor false) target := by
  constructor
  · exact view.cursor
  · exact hactive.symm.trans view.halted
  · exact view.truth
  · exact view.written
  · exact view.reviews
  · exact view.reported
  · exact view.commitments_forward
  · exact view.commitments_reverse
  · intro b hb
    obtain ⟨a, ha, hs, ht⟩ := view.executions_reverse b hb
    exact ⟨a, List.mem_append_left _ ha, hs, ht⟩

/-- The implemented bounded old-execution settling preserves the view on
the exact original run state at the returned original clock. -/
theorem HistorySuffixStateView.settleOld (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (fuel n : ℕ) (target : State (I.freshSuffix first))
    (view : HistorySuffixStateView input first (run input C mode accounting rule sample n) target) :
    let result := settleOldExecutions first accounting rule fuel sample.1
      (publicStartup (run input C mode accounting rule sample n))
    HistorySuffixStateView input first (run input C mode accounting rule sample (n + result.2)) target := by
  induction fuel generalizing n with
  | zero => simpa only [settleOldExecutions, Nat.add_zero] using view
  | succ fuel ih =>
    generalize hn : silentOldNext first accounting (publicStartup (run input C mode accounting rule sample n))
      (rule sample.1 (publicStartup (run input C mode accounting rule sample n)).history) = next
    cases next with
    | none => simpa only [settleOldExecutions, hn, Nat.add_zero] using view
    | some next =>
      obtain ⟨ha, handle, tool, haction, hold, hnext⟩ :=
        (silentOldNext_some_iff first accounting _ next _).mp hn
      obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample n
      obtain ⟨sourceNext, hs⟩ := hlegal sample.1 _ _ m _ hp ha
      have hr := run_succ_of_step input C mode accounting rule sample n sourceNext ha hs
      change rule sample.1 (run input C mode accounting rule sample n).history = .execute handle tool at haction
      have hv : HistorySuffixStateView input first (run input C mode accounting rule sample (n + 1)) target := by
        rw [hr]
        rw [haction] at hs
        cases hs
        exact view.executeOld input first accounting handle tool hold ha
      have ht := ih (n + 1) hv
      have hnActual := silentOldNext_actual input C mode accounting rule hlegal sample first n next hn
      rw [← hnActual] at ht
      simp only [settleOldExecutions, hn]
      rw [show n + ((settleOldExecutions first accounting rule fuel sample.1 next).2 + 1) =
        (n + 1) + (settleOldExecutions first accounting rule fuel sample.1 next).2 by omega]
      exact ht

@[simp] theorem suffixStageOf_eq_iff (first : ℕ) (left right : I.Stage)
    (hl : first ≤ left.val) (hr : first ≤ right.val) :
    suffixStageOf first left hl = suffixStageOf first right hr ↔ left = right := by
  constructor
  · intro he
    have hh := congrArg (I.freshStageLift first) he
    simpa only [freshStageLift_suffixStageOf] using hh
  · rintro rfl
    rfl

theorem suffixHandleOf_append_noWrite (first : ℕ)
    (history events : List (VisibleEvent (I.freshSuffix first)))
    (handle : MismatchHandle I) (hf : first ≤ handle.stage.val)
    (hclear : events.filterMap (eventWrite (suffixStageOf first handle.stage hf)) = []) :
    suffixHandleOf first (history ++ events) handle hf = suffixHandleOf first history handle hf := by
  simp only [suffixHandleOf, historyWriteSerial, historyWrite, List.filterMap_append, hclear, List.append_nil]

/-- Frame only the ledger relations used by the replay induction. This
lemma handles genuine non-allocation/non-execution steps below; every premise
is an elementary field identity established from those actual transitions. -/
theorem HistorySuffixStateView.frame (input : StatisticalInput I) (first : ℕ)
    {source sourceNext : State I} {target targetNext : State (I.freshSuffix first)}
    (view : HistorySuffixStateView input first source target)
    (hcursor : sourceNext.cursor = first + targetNext.cursor)
    (hhalted : sourceNext.halted = targetNext.halted)
    (htruth : ∀ stage (hf : first ≤ stage.val),
      targetNext.ledger.truth (suffixStageOf first stage hf) = sourceNext.ledger.truth stage)
    (hwritten : ∀ stage (hf : first ≤ stage.val),
      targetNext.ledger.written (suffixStageOf first stage hf) = sourceNext.ledger.written stage)
    (hreviews : ∀ stage (hf : first ≤ stage.val),
      targetNext.ledger.reviews (suffixStageOf first stage hf) = sourceNext.ledger.reviews stage)
    (hreported : ∀ stage (hf : first ≤ stage.val),
      (∃ t, sourceNext.ledger.reportTime stage = some t) →
        ∃ t, targetNext.ledger.reportTime (suffixStageOf first stage hf) = some t)
    (hscomm : sourceNext.ledger.commitments = source.ledger.commitments)
    (htcomm : targetNext.ledger.commitments = target.ledger.commitments)
    (hsexec : sourceNext.ledger.executions = source.ledger.executions)
    (htexec : targetNext.ledger.executions = target.ledger.executions)
    (hhandles : ∀ a ∈ source.ledger.commitments, ∀ hf : first ≤ a.handle.stage.val,
      suffixHandleOf first targetNext.history a.handle hf = suffixHandleOf first target.history a.handle hf) :
    HistorySuffixStateView input first sourceNext targetNext := by
  refine ⟨hcursor, hhalted, htruth, hwritten, hreviews, hreported, ?_, ?_, ?_⟩
  · intro a ha hf
    rw [hscomm] at ha
    obtain ⟨b, hb, hh, ht⟩ := view.commitments_forward a ha hf
    exact ⟨b, htcomm.symm ▸ hb, hh.trans (hhandles a ha hf).symm, ht⟩
  · intro b hb
    rw [htcomm] at hb
    obtain ⟨a, ha, hs, ht⟩ := view.commitments_reverse b hb
    exact ⟨a, hscomm.symm ▸ ha, hs, ht⟩
  · intro b hb
    rw [htexec] at hb
    obtain ⟨a, ha, hs, ht⟩ := view.executions_reverse b hb
    exact ⟨a, hsexec.symm ▸ ha, hs, ht⟩

/-- The elementary replay view is preserved by TWO actual native steps
with the dynamically projected action. This proves a transition fact,
not an assumed all-run alignment. -/
theorem HistorySuffixStateView.next (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (hearly : C.reporting = .early) (mode : ResourceMode)
    (accounting : NormalAccounting I) (sourceTapes : ReviewTapes input)
    (targetTapes : ReviewTapes (input.freshSuffix first))
    {source sourceNext : State I} {target targetNext : State (I.freshSuffix first)}
    (hinv : Invariant C source)
    (view : HistorySuffixStateView input first source target)
    {action : Action I} {targetAction : Action (I.freshSuffix first)}
    (haction : suffixActionOf first target.history action = some targetAction)
    (hs : Step input C mode accounting sourceTapes source action sourceNext)
    (ht : Step (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetTapes target targetAction targetNext) :
    HistorySuffixStateView input first sourceNext targetNext := by
  cases hs with
  | review stage live port resources =>
    simp only [suffixActionOf] at haction
    split at haction
    next hf =>
      cases haction
      cases ht
      apply view.frame input first
      · exact view.cursor
      · rfl
      · exact view.truth
      · exact view.written
      · intro future hfuture
        change Function.update target.ledger.reviews (suffixStageOf first stage hf)
          (target.ledger.reviews (suffixStageOf first stage hf) + 1) (suffixStageOf first future hfuture) =
          Function.update source.ledger.reviews stage (source.ledger.reviews stage + 1) future
        simp only [Function.update_apply, suffixStageOf_eq_iff]
        split <;> simp_all only [view.reviews]
      · exact view.reported
      · rfl
      · rfl
      · rfl
      · rfl
      · intro a _ hfuture
        apply suffixHandleOf_append_noWrite
        rfl
    next hf => cases haction
  | write stage bit live port resources =>
    simp only [suffixActionOf] at haction
    split at haction
    next hf =>
      cases haction
      cases ht
      apply view.frame input first
      · exact view.cursor
      · rfl
      · intro future hfuture
        simp only [record, reportedWriteLedger_truth]
        exact view.truth future hfuture
      · intro future hfuture
        simp only [record, reportedWriteLedger, hearly, currentRelaxedContract, ↓reduceIte, writeLedger]
        simp only [Function.update_apply, suffixStageOf_eq_iff]
        split <;> simp_all only [view.written]
      · simpa only [record, reportedWriteLedger, hearly, currentRelaxedContract, ↓reduceIte, writeLedger] using view.reviews
      · intro future hfuture hreported
        change ∃ t, (reportedWriteLedger (currentRelaxedContract (I.freshSuffix first)) target
          (suffixStageOf first stage hf) bit).reportTime (suffixStageOf first future hfuture) = some t
        simp only [record, reportedWriteLedger, hearly, currentRelaxedContract, ↓reduceIte, writeLedger] at hreported ⊢
        simp only [Function.update_apply, suffixStageOf_eq_iff] at hreported ⊢
        split at hreported
        next heq => subst future; exact ⟨target.clock, by simp only [↓reduceIte]⟩
        next hne =>
          simp only [hne, ↓reduceIte]
          exact view.reported future hfuture hreported
      · simp only [record, reportedWriteLedger, hearly, ↓reduceIte, writeLedger]
      · rfl
      · simp only [record, reportedWriteLedger, hearly, ↓reduceIte, writeLedger]
      · rfl
      · intro a ha hfuture
        apply suffixHandleOf_append_noWrite
        have hne := hinv.commitment_ne_open port ha
        have hd : suffixStageOf first stage hf ≠ suffixStageOf first a.handle.stage hfuture := by
          intro he
          exact hne ((suffixStageOf_eq_iff first stage a.handle.stage hf hfuture).mp he).symm
        simp only [writeResponses, currentRelaxedContract, ↓reduceIte, writeLedger,
          List.singleton_append, List.filterMap_cons, List.filterMap_nil, eventWrite, hd, ↓reduceIte]
    next hf => cases haction
  | allocate handle tool active valid compatible unused unallocated window resources =>
    simp only [suffixActionOf] at haction
    split at haction
    next hf =>
      cases haction
      cases ht
      constructor
      · exact view.cursor
      · rfl
      · exact view.truth
      · exact view.written
      · exact view.reviews
      · exact view.reported
      · intro a ha hfuture
        change a ∈ source.ledger.commitments ++ [⟨handle, tool, source.clock⟩] at ha
        rcases List.mem_append.mp ha with hold | hnew
        · obtain ⟨b, hb, hh, ht⟩ := view.commitments_forward a hold hfuture
          refine ⟨b, List.mem_append_left _ hb, ?_, ht⟩
          rw [hh]
          symm
          apply suffixHandleOf_append_noWrite
          rfl
        · obtain rfl := List.mem_singleton.mp hnew
          refine ⟨⟨suffixHandleOf first target.history handle hf, tool, target.clock⟩,
            List.mem_append_right _ (List.mem_singleton_self _), ?_, rfl⟩
          symm
          apply suffixHandleOf_append_noWrite
          rfl
      · intro b hb
        change b ∈ target.ledger.commitments ++ [⟨suffixHandleOf first target.history handle hf, tool, target.clock⟩] at hb
        rcases List.mem_append.mp hb with hold | hnew
        · obtain ⟨a, ha, hs, ht⟩ := view.commitments_reverse b hold
          exact ⟨a, List.mem_append_left _ ha, hs, ht⟩
        · obtain rfl := List.mem_singleton.mp hnew
          exact ⟨⟨handle, tool, source.clock⟩, List.mem_append_right _ (List.mem_singleton_self _),
            (freshStageLift_suffixStageOf first handle.stage hf).symm, rfl⟩
      · exact view.executions_reverse
    next hf => cases haction
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    simp only [suffixActionOf] at haction
    split at haction
    next hf =>
      cases haction
      cases ht
      constructor
      · exact view.cursor
      · rfl
      · exact view.truth
      · exact view.written
      · exact view.reviews
      · exact view.reported
      · intro a ha hfuture
        obtain ⟨b, hb, hh, ht⟩ := view.commitments_forward a ha hfuture
        refine ⟨b, hb, ?_, ht⟩
        rw [hh]
        symm
        apply suffixHandleOf_append_noWrite
        rfl
      · exact view.commitments_reverse
      · intro b hb
        change b ∈ target.ledger.executions ++ [⟨suffixHandleOf first target.history handle hf, tool, target.clock⟩] at hb
        rcases List.mem_append.mp hb with hold | hnew
        · obtain ⟨a, ha, hs, ht⟩ := view.executions_reverse b hold
          exact ⟨a, List.mem_append_left _ ha, hs, ht⟩
        · obtain rfl := List.mem_singleton.mp hnew
          exact ⟨⟨handle, tool, source.clock⟩, List.mem_append_right _ (List.mem_singleton_self _),
            (freshStageLift_suffixStageOf first handle.stage hf).symm, rfl⟩
    next hf => cases haction
  | advance stage live written resources =>
    simp only [suffixActionOf] at haction
    split at haction
    next hf =>
      cases haction
      cases ht
      apply view.frame input first
      · have hc := view.cursor
        change source.cursor + 1 = first + (target.cursor + 1)
        omega
      · rfl
      · exact view.truth
      · exact view.written
      · exact view.reviews
      · exact view.reported
      · rfl
      · rfl
      · rfl
      · rfl
      · intro a _ hfuture
        apply suffixHandleOf_append_noWrite
        rfl
    next hf => cases haction
  | stop active =>
    cases haction
    cases ht
    apply view.frame input first
    · exact view.cursor
    · rfl
    · exact view.truth
    · exact view.written
    · exact view.reviews
    · exact view.reported
    · rfl
    · rfl
    · rfl
    · rfl
    · intro a _ hfuture
      apply suffixHandleOf_append_noWrite
      rfl
  | abandon active =>
    cases haction
    cases ht
    apply view.frame input first
    · exact view.cursor
    · rfl
    · exact view.truth
    · exact view.written
    · exact view.reviews
    · exact view.reported
    · rfl
    · rfl
    · rfl
    · rfl
    · intro a _ hfuture
      apply suffixHandleOf_append_noWrite
      rfl

end PaperProofs.Common.Native
