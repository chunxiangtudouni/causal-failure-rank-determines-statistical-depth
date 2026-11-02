module

public import PaperProofs.Common.NativeFreshness

/-!
Pathwise causal invariants of the actual native transition system. These are
derived from `Step` and `Prefix`, rather than imposed on states or policies.
-/

@[expose] public section

open MeasureTheory

namespace PaperProofs.Common.Native

variable {I : Instance}

/-- No strictly future stage has been written or reviewed. The current stage
may already have been used; the terminal cursor is allowed to equal N. -/
structure CursorInvariant (s : State I) : Prop where
  bound : s.cursor ≤ I.stageCount
  future_written : ∀ i : I.Stage, s.cursor < i.val → s.ledger.written i = none
  future_reviews : ∀ i : I.Stage, s.cursor < i.val → s.ledger.reviews i = 0

theorem initial_cursorInvariant (truth : I.Stage → Bool) :
    CursorInvariant (initial truth) := by
  constructor
  · exact Nat.zero_le _
  · intros; rfl
  · intros; rfl

theorem step_cursor_bounds (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (h : Step input C mode accounting tapes s action s') :
    s.cursor ≤ s'.cursor ∧ s'.cursor ≤ s.cursor + 1 := by
  cases h <;> simp [record, stopState]

theorem step_cursorInvariant (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I} (hinv : CursorInvariant s)
    (h : Step input C mode accounting tapes s action s') : CursorInvariant s' := by
  classical
  cases h with
  | review i live port resources =>
    refine ⟨hinv.bound, ?_, ?_⟩
    · exact hinv.future_written
    · intro j hj
      have hne : j ≠ i := by intro he; subst j; exact (Nat.lt_irrefl _ (live.2 ▸ hj))
      simpa only [record, reviewLedger, Function.update_of_ne hne] using hinv.future_reviews j hj
  | write i bit live port resources =>
    refine ⟨hinv.bound, ?_, ?_⟩
    · intro j hj
      have hne : j ≠ i := by intro he; subst j; exact (Nat.lt_irrefl _ (live.2 ▸ hj))
      simp only [record, reportedWriteLedger]
      split_ifs <;> simpa only [writeLedger, Function.update_of_ne hne] using hinv.future_written j hj
    · intro j hj
      simp only [record, reportedWriteLedger]
      split_ifs <;> exact hinv.future_reviews j hj
  | allocate handle tool active valid compatible unused unallocated window resources =>
    exact ⟨hinv.bound, hinv.future_written, hinv.future_reviews⟩
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    exact ⟨hinv.bound, hinv.future_written, hinv.future_reviews⟩
  | advance i live written resources =>
    refine ⟨?_, ?_, ?_⟩
    · change s.cursor + 1 ≤ I.stageCount
      have hi : i.val < I.stageCount := i.isLt
      have hc := live.2
      omega
    · intro j hj
      exact hinv.future_written j (by change s.cursor + 1 < j.val at hj; omega)
    · intro j hj
      exact hinv.future_reviews j (by change s.cursor + 1 < j.val at hj; omega)
  | stop active => exact ⟨hinv.bound, hinv.future_written, hinv.future_reviews⟩
  | abandon active => exact ⟨hinv.bound, hinv.future_written, hinv.future_reviews⟩

theorem prefix_cursorInvariant (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s) : CursorInvariant s := by
  induction hp with
  | initial => exact initial_cursorInvariant truth
  | next _ step ih => exact step_cursorInvariant input C mode accounting tapes ih step

theorem run_cursorInvariant (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting policy)
    (sample : Seed × input.World) (n : ℕ) :
    CursorInvariant (run input C mode accounting policy sample n) := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C mode accounting policy hlegal sample n
  exact prefix_cursorInvariant input C mode accounting policy sample.1 _ _ hp

theorem CursorInvariant.validHandle_le {s : State I} (hinv : CursorInvariant s)
    {handle : MismatchHandle I} (hvalid : validHandle s handle) :
    handle.stage.val ≤ s.cursor := by
  by_contra h
  have hw := hinv.future_written handle.stage (Nat.lt_of_not_ge h)
  have hv := hvalid.1
  rw [hw] at hv
  cases hv

theorem CursorInvariant.write_not_allWritten {s : State I} (hinv : CursorInvariant s)
    (next i : I.Stage) (hbefore : s.cursor < next.val) (hlive : liveStage s i) (bit : Bool) :
    ¬ allWritten (writeLedger s i bit) := by
  classical
  intro hall
  have hne : next ≠ i := by
    intro he
    subst next
    exact Nat.lt_irrefl _ (hlive.2 ▸ hbefore)
  exact hall next (by simpa only [writeLedger, Function.update_of_ne hne]
    using hinv.future_written next hbefore)

/-- Only the hidden truth field changes. Every public ledger field, the clock,
history, and cursor stay identical. This is used to compare actual runs, whose
full states cannot be equal when their unobserved future truths differ. -/
def retargetTruth (s : State I) (truth : I.Stage → Bool) : State I :=
  { s with ledger := { s.ledger with truth := truth } }

theorem retargetTruth_self (s : State I) : retargetTruth s s.ledger.truth = s := by
  rfl

theorem retargetTruth_initial (truth truth' : I.Stage → Bool) :
    retargetTruth (initial truth) truth' = initial truth' := rfl

theorem retargetTruth_record (accounting : NormalAccounting I) (s : State I)
    (action : Action I) (responses : List (VisibleEvent I)) (L : Ledger I)
    (cursor : ℕ) (halted : Bool) (truth : I.Stage → Bool) :
    retargetTruth (record accounting s action responses L cursor halted) truth =
      record accounting (retargetTruth s truth) action responses {L with truth := truth} cursor halted := rfl

theorem retargetTruth_stopState (s : State I) (abandon : Bool) (truth : I.Stage → Bool) :
    retargetTruth (stopState s abandon) truth = stopState (retargetTruth s truth) abandon := by
  classical
  simp only [stopState, retargetTruth, allWritten]
  rfl

theorem retargetTruth_withinResources (C : Contract I) (mode : ResourceMode)
    (s : State I) (truth : I.Stage → Bool) :
    withinResources C mode (retargetTruth s truth).ledger ↔ withinResources C mode s.ledger := by
  rfl

theorem writeResponses_retargetTruth (C : Contract I) {s : State I}
    (hinv : CursorInvariant s) (next i : I.Stage) (hbefore : s.cursor < next.val)
    (hlive : liveStage s i) (bit : Bool) (truth : I.Stage → Bool)
    (htruth : truth i = s.ledger.truth i) :
    writeResponses C (retargetTruth s truth) i bit = writeResponses C s i bit := by
  classical
  have hn := hinv.write_not_allWritten next i hbefore hlive bit
  have hn' : ¬ allWritten (writeLedger (retargetTruth s truth) i bit) := hn
  simp only [writeResponses]
  split_ifs with hearly
  · simp only [writeLedger, retargetTruth, htruth]
  · rfl

theorem reportedWriteLedger_retargetTruth (C : Contract I) (s : State I)
    (i : I.Stage) (bit : Bool) (truth : I.Stage → Bool) :
    reportedWriteLedger C (retargetTruth s truth) i bit =
      {reportedWriteLedger C s i bit with truth := truth} := by
  classical
  have hall : allWritten (writeLedger (retargetTruth s truth) i bit) ↔
      allWritten (writeLedger s i bit) := Iff.rfl
  by_cases he : C.reporting = .early
  · simp only [reportedWriteLedger, he, ↓reduceIte]
    rfl
  · by_cases ha : allWritten (writeLedger s i bit)
    · have ha' := hall.mpr ha
      simp only [reportedWriteLedger, he, ha, ha', ↓reduceIte]
      rfl
    · have ha' : ¬ allWritten (writeLedger (retargetTruth s truth) i bit) := ha ∘ hall.mp
      simp only [reportedWriteLedger, he, ha, ha', ↓reduceIte]
      rfl

/-- Transport a real legal step before `next` across changes to all future
truths and tapes. In particular this proves that no such step reads a future
observation port or reports a future hidden truth. -/
theorem step_retarget_before (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (tapes tapes' : ReviewTapes input) (truth : I.Stage → Bool) (next : I.Stage)
    {s s' : State I} {action : Action I} (hinv : CursorInvariant s)
    (hbefore : s.cursor < next.val)
    (htruth : ∀ i : I.Stage, i.val < next.val → truth i = s.ledger.truth i)
    (htapes : ∀ i : I.Stage, i.val < next.val → tapes' i = tapes i)
    (h : Step input C mode accounting tapes s action s') :
    Step input C mode accounting tapes' (retargetTruth s truth) action
      (retargetTruth s' truth) := by
  classical
  cases h with
  | review i live port resources =>
    have hi : i.val < next.val := by have hc := live.2; omega
    have ht := htapes i hi
    have hr : withinResources C mode (record accounting (retargetTruth s truth) (.review i)
        [.observation i (tapes' i (s.ledger.reviews i).toNat).val]
        (reviewLedger (retargetTruth s truth) i) s.cursor false).ledger := by
      simpa only [ht, withinResources, Ledger.obeysCaps, Ledger.totalCalls,
        record, retargetTruth, reviewLedger] using resources
    simpa only [retargetTruth_record, retargetTruth, reviewLedger, record, ht] using
      (Step.review (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes') (retargetTruth s truth) i live port hr)
  | write i bit live port resources =>
    have hi : i.val < next.val := by have hc := live.2; omega
    have hrsp := writeResponses_retargetTruth C hinv next i hbefore live bit truth (htruth i hi)
    have hr : withinResources C mode (record accounting (retargetTruth s truth) (.write i bit)
        (writeResponses C (retargetTruth s truth) i bit)
        (reportedWriteLedger C (retargetTruth s truth) i bit) s.cursor false).ledger := by
      rw [hrsp, reportedWriteLedger_retargetTruth]
      simpa only [withinResources, Ledger.obeysCaps,
        Ledger.totalCalls, record, retargetTruth] using resources
    have hs := Step.write (input := input) (C := C) (mode := mode) (accounting := accounting)
      (tapes := tapes') (retargetTruth s truth) i bit live port hr
    rw [hrsp, reportedWriteLedger_retargetTruth] at hs
    rw [retargetTruth_record]
    exact hs
  | allocate handle tool active valid compatible unused unallocated window resources =>
    have hi : handle.stage.val < next.val := lt_of_le_of_lt (hinv.validHandle_le valid) hbefore
    have hv : validHandle (retargetTruth s truth) handle := by
      simpa only [validHandle, retargetTruth, htruth handle.stage hi] using valid
    have hr : withinResources C mode (record accounting (retargetTruth s truth) (.allocate handle tool)
        [.committed handle tool] (allocateLedger (retargetTruth s truth) handle tool) s.cursor false).ledger := by
      simpa only [withinResources, Ledger.obeysCaps, Ledger.totalCalls,
        record, retargetTruth, allocateLedger] using resources
    simpa only [retargetTruth_record, retargetTruth, allocateLedger, record] using
      (Step.allocate (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes') (retargetTruth s truth) handle tool active hv compatible unused unallocated window hr)
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    have hi : handle.stage.val < next.val := lt_of_le_of_lt (hinv.validHandle_le valid) hbefore
    have hv : validHandle (retargetTruth s truth) handle := by
      simpa only [validHandle, retargetTruth, htruth handle.stage hi] using valid
    have hr : withinResources C mode (record accounting (retargetTruth s truth) (.execute handle tool)
        [.executed handle tool] (executeLedger (retargetTruth s truth) handle tool) s.cursor false).ledger := by
      simpa only [withinResources, Ledger.obeysCaps, Ledger.totalCalls,
        record, retargetTruth, executeLedger] using resources
    simpa only [retargetTruth_record, retargetTruth, executeLedger, record] using
      (Step.execute (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes') (retargetTruth s truth) handle tool active hv compatible committed unused uncorrected window hr)
  | advance i live written resources =>
    have hr : withinResources C mode (record accounting (retargetTruth s truth) (.advance i)
        [.advanced i] (advanceLedger (retargetTruth s truth) i) (s.cursor + 1) false).ledger := by
      simpa only [withinResources, Ledger.obeysCaps, Ledger.totalCalls,
        record, retargetTruth, advanceLedger] using resources
    simpa only [retargetTruth_record, retargetTruth, advanceLedger, record] using
      (Step.advance (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes') (retargetTruth s truth) i live written hr)
  | stop active =>
    simpa only [retargetTruth_stopState] using
      (Step.stop (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes') (retargetTruth s truth) active)
  | abandon active =>
    simpa only [retargetTruth_stopState] using
      (Step.abandon (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes') (retargetTruth s truth) active)

section Runs

variable {Seed : Type*}

theorem run_truth (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World) (n : ℕ) :
    (run input C mode accounting policy sample n).ledger.truth = input.truthAt sample.2 := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C mode accounting policy hlegal sample n
  exact prefix_truth input C mode accounting policy sample.1 _ _ hp

theorem run_cursor_step_bounds (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World) (n : ℕ) :
    (run input C mode accounting policy sample n).cursor ≤
        (run input C mode accounting policy sample (n + 1)).cursor ∧
      (run input C mode accounting policy sample (n + 1)).cursor ≤
        (run input C mode accounting policy sample n).cursor + 1 := by
  by_cases hh : (run input C mode accounting policy sample n).halted = true
  · rw [run_succ_of_halted input C mode accounting policy sample n hh]
    exact ⟨le_rfl, Nat.le_succ _⟩
  · have ha := Bool.eq_false_iff.mpr hh
    obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting policy hlegal sample n
    obtain ⟨s', hs⟩ := hlegal sample.1 _ _ m _ hp ha
    rw [run_succ_of_step input C mode accounting policy sample n s' ha hs]
    exact step_cursor_bounds input C mode accounting _ hs

theorem run_cursor_monotone (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World) :
    Monotone (fun n => (run input C mode accounting policy sample n).cursor) :=
  monotone_nat_of_le_succ fun n => (run_cursor_step_bounds input C mode accounting policy hlegal sample n).1

/-- Every finite prefix ending no later than the first entry is unchanged on
all public fields when the hidden world is replaced after the boundary. -/
theorem run_retarget_of_before (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (seed : Seed)
    (world world' : input.World) (next : I.Stage)
    (hpast : ∀ i : I.Stage, i.val < next.val → world' i = world i) (n : ℕ)
    (hbefore : ∀ k < n, (run input C mode accounting policy (seed, world) k).cursor < next.val) :
    run input C mode accounting policy (seed, world') n =
      retargetTruth (run input C mode accounting policy (seed, world) n) (input.truthAt world') := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq := ih (fun k hk => hbefore k (Nat.lt_succ_of_lt hk))
    by_cases hh : (run input C mode accounting policy (seed, world) n).halted = true
    · have hh' : (run input C mode accounting policy (seed, world') n).halted = true := by
        rw [heq]; exact hh
      rw [run_succ_of_halted input C mode accounting policy (seed, world) n hh,
        run_succ_of_halted input C mode accounting policy (seed, world') n hh']
      exact heq
    · have ha := Bool.eq_false_iff.mpr hh
      obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting policy hlegal (seed, world) n
      obtain ⟨s', hs⟩ := hlegal seed _ _ m _ hp ha
      have htruth : ∀ i : I.Stage, i.val < next.val → input.truthAt world' i =
          (run input C mode accounting policy (seed, world) n).ledger.truth i := by
        intro i hi
        rw [run_truth input C mode accounting policy hlegal]
        exact congrArg Prod.fst (hpast i hi)
      have htapes : ∀ i : I.Stage, i.val < next.val → worldTapes input world' i = worldTapes input world i := by
        intro i hi
        exact congrArg Prod.snd (hpast i hi)
      have htransport := step_retarget_before input C mode accounting
        (worldTapes input world) (worldTapes input world') (input.truthAt world') next
        (run_cursorInvariant input C mode accounting policy hlegal (seed, world) n)
        (hbefore n (Nat.lt_succ_self n)) htruth htapes hs
      have ha' : (run input C mode accounting policy (seed, world') n).halted = false := by
        rw [heq]; exact ha
      have hs' : Step input C mode accounting (worldTapes input world')
          (run input C mode accounting policy (seed, world') n)
          (policy seed (run input C mode accounting policy (seed, world') n).history)
          (retargetTruth s' (input.truthAt world')) := by
        rw [heq]
        exact htransport
      rw [run_succ_of_step input C mode accounting policy (seed, world) n s' ha hs,
        run_succ_of_step input C mode accounting policy (seed, world') n _ ha' hs']

theorem entryHistory_some_transport (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (seed : Seed)
    (world world' : input.World) (next : I.Stage)
    (hpast : ∀ i : I.Stage, i.val < next.val → world' i = world i)
    (history : List (VisibleEvent I))
    (hentry : entryHistory input C mode accounting policy next (seed, world) = some history) :
    entryHistory input C mode accounting policy next (seed, world') = some history := by
  obtain ⟨n, hn, hminimal, hhistory⟩ :=
    (entryHistory_some_iff input C mode accounting policy next (seed, world) history).mp hentry
  have hbefore : ∀ k < n, (run input C mode accounting policy (seed, world) k).cursor < next.val := by
    intro k hk
    have hle := run_cursor_monotone input C mode accounting policy hlegal (seed, world) hk.le
    change (run input C mode accounting policy (seed, world) k).cursor ≤
      (run input C mode accounting policy (seed, world) n).cursor at hle
    rw [hn] at hle
    exact lt_of_le_of_ne hle (hminimal k hk)
  have heq := run_retarget_of_before input C mode accounting policy hlegal seed world world' next hpast n hbefore
  apply (entryHistory_some_iff input C mode accounting policy next (seed, world') history).mpr
  refine ⟨n, ?_, ?_, ?_⟩
  · rw [heq]; exact hn
  · intro k hk
    have heqk := run_retarget_of_before input C mode accounting policy hlegal seed world world' next hpast k
      (fun j hj => hbefore j (hj.trans hk))
    rw [heqk]
    exact hminimal k hk
  · rw [heq]; exact hhistory

/-- Actual entry history is determined by the seed and the strictly earlier
stages, including the outcome `none` when that stage is never entered. -/
theorem entryHistory_eq_of_past (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (seed : Seed)
    (world world' : input.World) (next : I.Stage)
    (hpast : ∀ i : I.Stage, i.val < next.val → world' i = world i) :
    entryHistory input C mode accounting policy next (seed, world') =
      entryHistory input C mode accounting policy next (seed, world) := by
  cases he : entryHistory input C mode accounting policy next (seed, world) with
  | some history =>
    exact entryHistory_some_transport input C mode accounting policy hlegal seed world world' next hpast history he
  | none =>
    cases he' : entryHistory input C mode accounting policy next (seed, world') with
    | none => rfl
    | some history =>
      have hc := entryHistory_some_transport input C mode accounting policy hlegal seed world' world next
        (fun i hi => (hpast i hi).symm) history he'
      rw [he] at hc
      cases hc

end Runs

/-- A fixed completion is only an analysis device. It is not queried by the
policy and need not have any special truth or probability. -/
noncomputable def completePastWorld (input : StatisticalInput I) (next : I.Stage)
    (past : input.PastWorld next) : input.World := fun i =>
  if hi : i.val < next.val then past ⟨i, hi⟩
  else (false, fun _ => Classical.choose ((input.experiment i).channelPMF false).support_nonempty)

theorem completePastWorld_apply_past (input : StatisticalInput I) (next : I.Stage)
    (past : input.PastWorld next) (i : I.Stage) (hi : i.val < next.val) :
    completePastWorld input next past i = past ⟨i, hi⟩ := by
  simp only [completePastWorld, hi, ↓reduceDIte]

theorem measurable_completePastWorld (input : StatisticalInput I) (next : I.Stage) :
    Measurable (completePastWorld input next) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i.val < next.val
  · simpa only [completePastWorld, hi, ↓reduceDIte] using
      (measurable_pi_apply (⟨i, hi⟩ : {i : I.Stage // i.val < next.val}))
  · simpa only [completePastWorld, hi, ↓reduceDIte] using
      (measurable_const : Measurable (fun _ : input.PastWorld next =>
        (false, fun _ : ℕ => Classical.choose ((input.experiment i).channelPMF false).support_nonempty)))

/-- Unconditional causal factorization for the original legal measurable native
policy class. The proof constructs its record by fixed future completion and
uses the actual transition-based replacement theorem above. -/
theorem nativePreBirthFactorization (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) :
    NativePreBirthFactorization input C mode accounting := by
  intro Seed m
  let : MeasurableSpace Seed := m
  intro policy next
  let complete : Seed × input.PastWorld next → Seed × input.World :=
    fun sample => (sample.1, completePastWorld input next sample.2)
  have hm : Measurable complete :=
    measurable_fst.prodMk ((measurable_completePastWorld input next).comp measurable_snd)
  refine ⟨fun sample => entryHistory input C mode accounting policy.rule next (complete sample),
    (measurable_entryHistory input C mode accounting policy.rule policy.measurable_rule next).comp hm, ?_⟩
  rintro ⟨seed, world⟩
  exact (entryHistory_eq_of_past input C mode accounting policy.rule policy.legal seed world
    (completePastWorld input next (fun i => world i.val)) next
    (fun i hi => completePastWorld_apply_past input next (fun i => world i.val) i hi)).symm

section Freshness

variable {Seed : Type} [MeasurableSpace Seed]

/-- Real native pre-birth history is independent of the next hidden truth and
complete potential tape, without a causal-factorization premise. -/
theorem entryHistory_independent_next (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) :
    ProbabilityTheory.IndepFun (entryHistory input C mode accounting policy.rule next)
      (fun sample : Seed × input.World => sample.2 next) (input.seededWorldLaw ν) :=
  entryHistory_independent_next_of_factorization input C mode accounting
    (nativePreBirthFactorization input C mode accounting) policy ν next

theorem entryHistory_jointLaw (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) :
    (input.seededWorldLaw ν).map (fun sample =>
        (entryHistory input C mode accounting policy.rule next sample, sample.2 next)) =
      ((input.seededWorldLaw ν).map (entryHistory input C mode accounting policy.rule next)).prod
        (input.stageLaw next) :=
  entryHistory_jointLaw_of_factorization input C mode accounting
    (nativePreBirthFactorization input C mode accounting) policy ν next

end Freshness

end PaperProofs.Common.Native
