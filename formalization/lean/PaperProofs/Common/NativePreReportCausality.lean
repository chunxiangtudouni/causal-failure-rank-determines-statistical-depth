module

public import PaperProofs.Common.NativePreReport
public import PaperProofs.Common.NativeObservedWords
public import PaperProofs.Common.NativeCapTransfer
public import Mathlib.Data.List.TakeWhile

/-!
Actual late-report prefixes before the first truth response. The analysis
retargets hidden truth in the existing Native.State; that state is never a
policy seed or part of the public pre-report record. Only actually observed
tape letters need agree. The final ordinary write in the report packet is
retained by event-level truncation.

This module supplies deterministic prefix/cylinder foundations only. It does
not postulate the product-posterior target or a common trace-likelihood factor.
-/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PaperProofs.Common.Native

variable {I : Instance}

def ReportFree (history : List (VisibleEvent I)) : Prop :=
  ∀ event ∈ history, beforeTruthReport event = true

theorem reportFree_append_left (history suffix : List (VisibleEvent I))
    (h : ReportFree (history ++ suffix)) : ReportFree history :=
  fun event he => h event (List.mem_append_left suffix he)

theorem step_history_extends (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next) :
    ∃ suffix, next.history = s.history ++ suffix := by
  cases hs <;> exact ⟨_, rfl⟩

theorem step_reportFree_source (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next)
    (hf : ReportFree next.history) : ReportFree s.history := by
  obtain ⟨suffix, hh⟩ := step_history_extends input C mode accounting tapes hs
  rw [hh] at hf
  exact reportFree_append_left _ _ hf

theorem reportFree_write_not_allWritten (C : Contract I) (hlate : C.reporting = .late)
    (accounting : NormalAccounting I) (s : State I) (i : I.Stage) (bit : Bool)
    (hf : ReportFree (record accounting s (.write i bit) (writeResponses C s i bit)
      (reportedWriteLedger C s i bit) s.cursor false).history) :
    ¬ allWritten (writeLedger s i bit) := by
  intro hall
  have hrsp : writeResponses C s i bit = [.wrote i bit s.clock] ++ reportAll (writeLedger s i bit) := by
    simp [writeResponses, hlate, hall]
  let event : VisibleEvent I := .report i ((writeLedger s i bit).truth i) ((writeLedger s i bit).writeSerial i)
  have hmem : event ∈ reportAll (writeLedger s i bit) := List.mem_ofFn.mpr ⟨i, rfl⟩
  have hfull : event ∈ (record accounting s (.write i bit) (writeResponses C s i bit)
      (reportedWriteLedger C s i bit) s.cursor false).history := by
    change event ∈ s.history ++ writeResponses C s i bit
    rw [hrsp]
    exact List.mem_append_right _ (List.mem_append_right _ hmem)
  have h := hf event hfull
  cases h

/-- No truth report has been fabricated in the ledger merely because a
State contains hidden truth. Report clocks come from actual response packets. -/
theorem prefix_reportTime_none_of_reportFree (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) (hf : ReportFree s.history) :
    ∀ i, s.ledger.reportTime i = none := by
  induction hp with
  | initial => intro i; rfl
  | @next n s next earlier step ih =>
    have hbefore := step_reportFree_source input C mode accounting tapes step hf
    have hclear := ih hbefore
    generalize haction : rule seed s.history = action at step
    cases step with
    | review => exact hclear
    | write i bit live port resources =>
      have hn := reportFree_write_not_allWritten C hlate accounting s i bit hf
      have hearly : C.reporting ≠ .early := by rw [hlate]; decide
      intro j
      change (reportedWriteLedger C s i bit).reportTime j = none
      simp only [reportedWriteLedger, hearly, ↓reduceIte, hn]
      exact hclear j
    | allocate handle tool active valid compatible unused unallocated window resources =>
      obtain ⟨t, ht⟩ := valid.2.2
      rw [hclear handle.stage] at ht
      cases ht
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      obtain ⟨t, ht⟩ := valid.2.2
      rw [hclear handle.stage] at ht
      cases ht
    | advance | stop | abandon => exact hclear

theorem prefix_no_corrections_of_reportFree (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) (hf : ReportFree s.history) :
    s.ledger.commitments = [] ∧ s.ledger.executions = [] := by
  have hclear := prefix_reportTime_none_of_reportFree input C hlate mode accounting rule seed truth tapes hp hf
  have hwf := prefix_ledgerWellFormed input C mode accounting rule seed truth tapes hp
  have hc : s.ledger.commitments = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    obtain ⟨t, ht, _⟩ := hwf.reported a ha
    rw [hclear a.handle.stage] at ht
    cases ht
  refine ⟨hc, List.eq_nil_iff_forall_not_mem.mpr ?_⟩
  intro e he
  obtain ⟨a, ha, _⟩ := hwf.backed e he
  rw [hc] at ha
  cases ha

def PreReportAction : Action I → Prop
  | .allocate _ _ | .execute _ _ => False
  | .review _ | .write _ _ | .advance _ | .stop | .abandon => True

/-- This classification includes the write whose same response packet
emits the first truth reports. Only the SOURCE must be report-free. -/
theorem step_preReportAction (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s next : State I} {action : Action I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) (hf : ReportFree s.history)
    (hs : Step input C mode accounting tapes s action next) : PreReportAction action := by
  have hclear := prefix_reportTime_none_of_reportFree input C hlate mode accounting rule seed truth tapes hp hf
  cases hs with
  | review | write | advance | stop | abandon => trivial
  | allocate handle tool active valid compatible unused unallocated window resources =>
    obtain ⟨t, ht⟩ := valid.2.2
    rw [hclear handle.stage] at ht
    cases ht
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    obtain ⟨t, ht⟩ := valid.2.2
    rw [hclear handle.stage] at ht
    cases ht

theorem reportAll_takeWhile_beforeTruthReport (L : Ledger I) :
    (reportAll L).takeWhile beforeTruthReport = [] := by
  have hfalse : ∀ event ∈ reportAll L, beforeTruthReport event = false := by
    intro event he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    rfl
  cases hh : reportAll L with
  | nil => rfl
  | cons event rest =>
    have hf := hfalse event (by simp [hh])
    simp [hf]

theorem late_writeResponses_takeWhile (C : Contract I) (hlate : C.reporting = .late)
    (s : State I) (i : I.Stage) (bit : Bool) :
    (writeResponses C s i bit).takeWhile beforeTruthReport = [.wrote i bit s.clock] := by
  classical
  by_cases hall : allWritten (writeLedger s i bit) <;>
    simp [writeResponses, hlate, hall, List.takeWhile_cons, beforeTruthReport, reportAll_takeWhile_beforeTruthReport]

theorem late_write_history_takeWhile (C : Contract I) (hlate : C.reporting = .late)
    (accounting : NormalAccounting I) (s : State I) (i : I.Stage) (bit : Bool) (hf : ReportFree s.history) :
    (record accounting s (.write i bit) (writeResponses C s i bit)
      (reportedWriteLedger C s i bit) s.cursor false).history.takeWhile beforeTruthReport =
      s.history ++ [.wrote i bit s.clock] := by
  change (s.history ++ writeResponses C s i bit).takeWhile beforeTruthReport = _
  rw [List.takeWhile_append_of_pos hf, late_writeResponses_takeWhile C hlate]

/-- Change all hidden truth values in a real report-free step. At a review,
only the actually purchased tape letter must be preserved. -/
theorem step_retarget_reportFree (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    (tapes tapes' : ReviewTapes input) (truth : I.Stage → Bool)
    {s next : State I} {action : Action I}
    (hclear : ∀ i, s.ledger.reportTime i = none)
    (hf : ReportFree next.history)
    (htape : ∀ i, action = .review i → tapes' i (s.ledger.reviews i).toNat = tapes i (s.ledger.reviews i).toNat)
    (hs : Step input C mode accounting tapes s action next) :
    Step input C mode accounting tapes' (retargetTruth s truth) action (retargetTruth next truth) := by
  classical
  cases hs with
  | review i live port resources =>
    have ht := htape i rfl
    have hr : withinResources C mode (record accounting (retargetTruth s truth) (.review i)
        [.observation i (tapes' i (s.ledger.reviews i).toNat).val]
        (reviewLedger (retargetTruth s truth) i) s.cursor false).ledger := by
      simpa only [ht, withinResources, Ledger.obeysCaps, Ledger.totalCalls,
        record, retargetTruth, reviewLedger] using resources
    simpa only [retargetTruth_record, retargetTruth, reviewLedger, record, ht] using
      (Step.review (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes') (retargetTruth s truth) i live port hr)
  | write i bit live port resources =>
    have hn := reportFree_write_not_allWritten C hlate accounting s i bit hf
    have hn' : ¬ allWritten (writeLedger (retargetTruth s truth) i bit) := hn
    have hearly : C.reporting ≠ .early := by rw [hlate]; decide
    have hrsp : writeResponses C (retargetTruth s truth) i bit = writeResponses C s i bit := by
      simp only [writeResponses, hearly, ↓reduceIte, hn, hn']
      rfl
    have hr : withinResources C mode (record accounting (retargetTruth s truth) (.write i bit)
        (writeResponses C (retargetTruth s truth) i bit)
        (reportedWriteLedger C (retargetTruth s truth) i bit) s.cursor false).ledger := by
      rw [hrsp, reportedWriteLedger_retargetTruth]
      simpa only [withinResources, Ledger.obeysCaps, Ledger.totalCalls, record, retargetTruth] using resources
    have hs' := Step.write (input := input) (C := C) (mode := mode) (accounting := accounting)
      (tapes := tapes') (retargetTruth s truth) i bit live port hr
    rw [hrsp, reportedWriteLedger_retargetTruth] at hs'
    rw [retargetTruth_record]
    exact hs'
  | allocate handle tool active valid compatible unused unallocated window resources =>
    obtain ⟨t, ht⟩ := valid.2.2
    rw [hclear handle.stage] at ht
    cases ht
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    obtain ⟨t, ht⟩ := valid.2.2
    rw [hclear handle.stage] at ht
    cases ht
  | advance i live written resources =>
    have hr : withinResources C mode (record accounting (retargetTruth s truth) (.advance i)
        [.advanced i] (advanceLedger (retargetTruth s truth) i) (s.cursor + 1) false).ledger := by
      simpa only [withinResources, Ledger.obeysCaps, Ledger.totalCalls, record, retargetTruth, advanceLedger] using resources
    simpa only [retargetTruth_record, retargetTruth, advanceLedger, record] using
      (Step.advance (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes') (retargetTruth s truth) i live written hr)
  | stop active =>
    simpa only [retargetTruth_stopState] using
      (Step.stop (input := input) (C := C) (mode := mode) (accounting := accounting) (tapes := tapes')
        (retargetTruth s truth) active)
  | abandon active =>
    simpa only [retargetTruth_stopState] using
      (Step.abandon (input := input) (C := C) (mode := mode) (accounting := accounting) (tapes := tapes')
        (retargetTruth s truth) active)

theorem step_historyObservations_length_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next) (i : I.Stage) :
    (historyObservations s.history i).length ≤ (historyObservations next.history i).length := by
  obtain ⟨suffix, hh⟩ := step_history_extends input C mode accounting tapes hs
  simp only [hh, historyObservations, List.filterMap_append, List.length_append]
  exact Nat.le_add_right _ _

theorem review_index_lt_next_observations (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} (i : I.Stage) (hs : Step input C mode accounting tapes s (.review i) next)
    (hcount : (historyObservations s.history i).length = (s.ledger.reviews i).toNat) :
    (s.ledger.reviews i).toNat < (historyObservations next.history i).length := by
  cases hs
  simp only [record, historyObservations, List.filterMap_append, List.length_append,
    List.filterMap_cons, eventObservation, ↓reduceIte, List.filterMap_nil, List.length_cons, List.length_nil]
  simpa only [historyObservations] using (show (s.ledger.reviews i).toNat <
    (historyObservations s.history i).length + 1 by omega)

/-- Replay an ACTUAL report-free Prefix after changing every hidden truth
and every unobserved review letter. The policy still receives its original
seed and public history only; this theorem adds no policy input. -/
theorem prefix_retarget_reportFree (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth truth' : I.Stage → Bool)
    (tapes tapes' : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) (hf : ReportFree s.history)
    (htape : ∀ i k, k < (historyObservations s.history i).length → tapes' i k = tapes i k) :
    Prefix input C mode accounting rule seed truth' tapes' n (retargetTruth s truth') := by
  induction hp with
  | initial => exact .initial
  | @next n s next earlier step ih =>
    have hbefore := step_reportFree_source input C mode accounting tapes step hf
    have hobs : ∀ i k, k < (historyObservations s.history i).length → tapes' i k = tapes i k := by
      intro i k hk
      exact htape i k (lt_of_lt_of_le hk (step_historyObservations_length_mono input C mode accounting tapes step i))
    have hprev := ih hbefore hobs
    have hclear := prefix_reportTime_none_of_reportFree input C hlate mode accounting rule seed truth tapes earlier hbefore
    have hread : ∀ i, rule seed s.history = .review i →
        tapes' i (s.ledger.reviews i).toNat = tapes i (s.ledger.reviews i).toNat := by
      intro i haction
      have hs : Step input C mode accounting tapes s (.review i) next := haction ▸ step
      exact htape i _ (review_index_lt_next_observations input C mode accounting tapes i hs
        (prefix_historyObservations_length_toNat input C mode accounting rule seed truth tapes earlier i))
    exact .next hprev (step_retarget_reportFree input C hlate mode accounting tapes tapes' truth' hclear hf hread step)

/-- This cylinder is computed from public observation strings only. It
contains no truth assignment, whole State, policy output or success event. -/
def publicWordCylinder (input : StatisticalInput I) (history : List (VisibleEvent I)) : Set (ReviewTapes input) :=
  {tapes | ∀ (i : I.Stage) (k : ℕ) (hk : k < (historyObservations history i).length),
    (tapes i k).val = (historyObservations history i)[k]}

theorem prefix_mem_publicWordCylinder (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    tapes ∈ publicWordCylinder input s.history := by
  intro i k hk
  exact (prefix_historyObservation_getElem input C mode accounting rule seed truth tapes hp i k hk).symm

theorem prefix_replay_of_publicWordCylinder (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth truth' : I.Stage → Bool)
    (tapes tapes' : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) (hf : ReportFree s.history)
    (hcyl : tapes' ∈ publicWordCylinder input s.history) :
    Prefix input C mode accounting rule seed truth' tapes' n (retargetTruth s truth') := by
  apply prefix_retarget_reportFree input C hlate mode accounting rule seed truth truth' tapes tapes' hp hf
  intro i k hk
  apply Fin.ext
  exact (hcyl i k hk).trans (prefix_historyObservation_getElem input C mode accounting rule seed truth tapes hp i k hk)

/-- Exact pointwise cylinder semantics for a fixed real public prefix,
uniform in ALL replacement truth assignments and all private seeds. -/
theorem prefix_retarget_iff_publicWordCylinder (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth truth' : I.Stage → Bool)
    (tapes tapes' : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) (hf : ReportFree s.history) :
    Prefix input C mode accounting rule seed truth' tapes' n (retargetTruth s truth') ↔
      tapes' ∈ publicWordCylinder input s.history := by
  constructor
  · intro hp'
    exact prefix_mem_publicWordCylinder input C mode accounting rule seed truth' tapes' (s := retargetTruth s truth') hp'
  · exact prefix_replay_of_publicWordCylinder input C hlate mode accounting rule seed truth truth' tapes tapes' hp hf

theorem measurableSet_publicWordCylinder (input : StatisticalInput I) (history : List (VisibleEvent I)) :
    MeasurableSet (publicWordCylinder input history) := by
  have heq : publicWordCylinder input history =
      ⋂ i : I.Stage, ⋂ k : Fin (historyObservations history i).length,
        {tapes : ReviewTapes input | (tapes i k.val).val = (historyObservations history i)[k.val]} := by
    ext tapes
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h i k
      exact h i k.val k.isLt
    · intro h i k hk
      exact h i ⟨k, hk⟩
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro k
  exact (measurableSet_singleton _).preimage
    ((measurable_of_countable (fun symbol : Fin (input.experiment i).alphabetSize => symbol.val)).comp
      ((measurable_pi_apply k.val).comp (measurable_pi_apply i)))

theorem prefix_iff_run_eq_of_clock (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) (n : ℕ) (s : State I)
    (hclock : s.clock = n) :
    Prefix input C mode accounting rule seed truth tapes n s ↔
      run input C mode accounting rule (seed, replayWorld input truth tapes) n = s := by
  constructor
  · exact prefix_eq_run input C mode accounting rule seed truth tapes
  · intro hrun
    obtain ⟨m, _hmn, hp⟩ := run_has_prefix input C mode accounting rule hlegal
      (seed, replayWorld input truth tapes) n
    rw [hrun] at hp
    have hmc : s.clock = m := prefix_clock input C mode accounting rule seed truth tapes hp
    have hmn : m = n := hmc.symm.trans hclock
    change Prefix input C mode accounting rule seed truth tapes m s at hp
    exact hmn ▸ hp

/-- A fixed reference-state parameter is only a proof witness. The private
seed remains exactly Seed, and the public gate inspects no sampled truth. -/
def prefixSeedGate (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) {Seed : Type*} (rule : PolicyRule I Seed)
    (tapes : ReviewTapes input) (n : ℕ) (s : State I) : Set Seed :=
  {seed | Prefix input C mode accounting rule seed s.ledger.truth tapes n s}

theorem measurableSet_prefixSeedGate (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*} [MeasurableSpace Seed]
    (rule : PolicyRule I Seed) (hm : MeasurableRule rule) (hlegal : LegalRule input C mode accounting rule)
    (tapes : ReviewTapes input) (n : ℕ) (s : State I) (hclock : s.clock = n) :
    MeasurableSet (prefixSeedGate input C mode accounting rule tapes n s) := by
  have heq : prefixSeedGate input C mode accounting rule tapes n s =
      {seed | run input C mode accounting rule (seed, replayWorld input s.ledger.truth tapes) n = s} := by
    ext seed
    exact prefix_iff_run_eq_of_clock input C mode accounting rule hlegal seed s.ledger.truth tapes n s hclock
  rw [heq]
  exact (measurableSet_singleton s).preimage
    ((measurable_run input C mode accounting rule hm n).comp (measurable_id.prodMk measurable_const))

/-- A REAL prefix event factors into a common private-seed gate and its
finite observation cylinder, for every replacement truth assignment. This
is a set identity, not a seed-singleton conditional-probability assertion. -/
theorem prefix_event_eq_seedGate_prod_cylinder (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (anchor : Seed) (truth truth' : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule anchor truth tapes n s) (hf : ReportFree s.history) :
    {sample : Seed × ReviewTapes input |
      Prefix input C mode accounting rule sample.1 truth' sample.2 n (retargetTruth s truth')} =
      prefixSeedGate input C mode accounting rule tapes n s ×ˢ publicWordCylinder input s.history := by
  have hc := prefix_mem_publicWordCylinder input C mode accounting rule anchor truth tapes hp
  ext sample
  constructor
  · intro hp'
    have hc' := prefix_mem_publicWordCylinder input C mode accounting rule sample.1 truth' sample.2
      (s := retargetTruth s truth') hp'
    have hback := prefix_replay_of_publicWordCylinder input C hlate mode accounting rule sample.1 truth'
      s.ledger.truth sample.2 tapes (s := retargetTruth s truth') hp' hf hc
    change Prefix input C mode accounting rule sample.1 s.ledger.truth tapes n s at hback
    exact ⟨hback, hc'⟩
  · rintro ⟨hseed, hc'⟩
    exact prefix_replay_of_publicWordCylinder input C hlate mode accounting rule sample.1 s.ledger.truth truth'
      tapes sample.2 hseed hf hc'

/-- Arbitrary seed events are retained; no positive-mass singleton, regular
conditional probability kernel or eventual-success restriction is needed. -/
theorem prefix_seedEvent_eq_rectangle (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (anchor : Seed) (truth truth' : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule anchor truth tapes n s) (hf : ReportFree s.history)
    (B : Set Seed) :
    {sample : Seed × ReviewTapes input | sample.1 ∈ B ∧
      Prefix input C mode accounting rule sample.1 truth' sample.2 n (retargetTruth s truth')} =
      (B ∩ prefixSeedGate input C mode accounting rule tapes n s) ×ˢ publicWordCylinder input s.history := by
  have heq := prefix_event_eq_seedGate_prod_cylinder input C hlate mode accounting rule anchor truth truth' tapes hp hf
  ext sample
  constructor
  · rintro ⟨hB, hp'⟩
    have hrect : sample ∈ prefixSeedGate input C mode accounting rule tapes n s ×ˢ publicWordCylinder input s.history := by
      rw [← heq]
      exact hp'
    exact ⟨⟨hB, hrect.1⟩, hrect.2⟩
  · rintro ⟨⟨hB, hseed⟩, hc⟩
    refine ⟨hB, ?_⟩
    have hrect : sample ∈ prefixSeedGate input C mode accounting rule tapes n s ×ˢ publicWordCylinder input s.history :=
      ⟨hseed, hc⟩
    rwa [← heq] at hrect

def worldWordCylinder (input : StatisticalInput I) (truth : I.Stage → Bool)
    (words : ∀ i, (input.experiment i).StoppedWord) : Set input.World :=
  Set.pi Set.univ (fun i => {truth i} ×ˢ (input.experiment i).prefixEvent (words i))

theorem measurableSet_worldWordCylinder (input : StatisticalInput I) (truth : I.Stage → Bool)
    (words : ∀ i, (input.experiment i).StoppedWord) : MeasurableSet (worldWordCylinder input truth words) :=
  MeasurableSet.pi Set.countable_univ fun i _ =>
    (measurableSet_singleton _).prod ((input.experiment i).measurableSet_prefixEvent (words i))

/-- Actual independent stage-law mass, retaining both the exact original
prior and every original likelihood factor. No alternate world law is used. -/
theorem worldLaw_worldWordCylinder (input : StatisticalInput I) (truth : I.Stage → Bool)
    (words : ∀ i, (input.experiment i).StoppedWord) :
    input.worldLaw (worldWordCylinder input truth words) =
      ∏ i, (input.experiment i).priorMass (truth i) *
        ENNReal.ofReal ((input.experiment i).wordProbability (truth i) (words i)) := by
  rw [StatisticalInput.worldLaw, worldWordCylinder, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [input.stageLaw_truth_tape, (input.experiment i).tapeLaw_prefixEvent]

theorem publicWordCylinder_iff_prefixEvents (input : StatisticalInput I) (history : List (VisibleEvent I))
    (hvalid : ∀ i symbol, symbol ∈ historyObservations history i → symbol < (input.experiment i).alphabetSize)
    (tapes : ReviewTapes input) :
    tapes ∈ publicWordCylinder input history ↔
      ∀ i, tapes i ∈ (input.experiment i).prefixEvent (historyObservationWord input history i (hvalid i)) := by
  constructor
  · intro hc i k
    apply Fin.ext
    exact hc i k.val k.isLt
  · intro hc i k hk
    exact congrArg Fin.val (hc i ⟨k, hk⟩)

/-- The seed gate is the SAME for every complete truth assignment. This
measurable event equality uses arbitrary seed events B, not seed singletons.
The observation words are the actual public Prefix words. -/
theorem prefix_jointTruth_seedEvent_eq_rectangle (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (anchor : Seed) (truth truth' : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule anchor truth tapes n s) (hf : ReportFree s.history)
    (hvalid : ∀ i symbol, symbol ∈ historyObservations s.history i → symbol < (input.experiment i).alphabetSize)
    (B : Set Seed) :
    {sample : Seed × input.World | sample.1 ∈ B ∧ input.truthAt sample.2 = truth' ∧
      Prefix input C mode accounting rule sample.1 truth' (worldTapes input sample.2) n (retargetTruth s truth')} =
      (B ∩ prefixSeedGate input C mode accounting rule tapes n s) ×ˢ
        worldWordCylinder input truth' (fun i => historyObservationWord input s.history i (hvalid i)) := by
  have heq := prefix_event_eq_seedGate_prod_cylinder input C hlate mode accounting rule anchor truth truth' tapes hp hf
  ext sample
  constructor
  · rintro ⟨hB, htruth, hp'⟩
    have hrect : (sample.1, worldTapes input sample.2) ∈
        prefixSeedGate input C mode accounting rule tapes n s ×ˢ publicWordCylinder input s.history := by
      rw [← heq]
      exact hp'
    refine ⟨⟨hB, hrect.1⟩, ?_⟩
    intro i _
    refine ⟨congrFun htruth i, ?_⟩
    exact ((publicWordCylinder_iff_prefixEvents input s.history hvalid _).mp hrect.2) i
  · rintro ⟨⟨hB, hseed⟩, hworld⟩
    have htruth : input.truthAt sample.2 = truth' := by
      funext i
      exact (hworld i (Set.mem_univ i)).1
    have hc : worldTapes input sample.2 ∈ publicWordCylinder input s.history := by
      apply (publicWordCylinder_iff_prefixEvents input s.history hvalid _).mpr
      intro i
      exact (hworld i (Set.mem_univ i)).2
    refine ⟨hB, htruth, ?_⟩
    have hrect : (sample.1, worldTapes input sample.2) ∈
        prefixSeedGate input C mode accounting rule tapes n s ×ˢ publicWordCylinder input s.history := ⟨hseed, hc⟩
    rwa [← heq] at hrect

/-- The first genuine likelihood-factorization interface. It concerns real
report-free Prefix endpoints, and NOT YET the full truncated preReportLaw.
All measurable seed events are allowed; failed and abandoned Prefixes stay. -/
theorem prefix_jointTruth_seedEvent_law (input : StatisticalInput I) (C : Contract I)
    (hlate : C.reporting = .late) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} [MeasurableSpace Seed] (rule : PolicyRule I Seed) (hm : MeasurableRule rule)
    (hlegal : LegalRule input C mode accounting rule) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (anchor : Seed) (truth truth' : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule anchor truth tapes n s) (hf : ReportFree s.history)
    (B : Set Seed) (hB : MeasurableSet B) :
    let event := {sample : Seed × input.World | sample.1 ∈ B ∧ input.truthAt sample.2 = truth' ∧
      Prefix input C mode accounting rule sample.1 truth' (worldTapes input sample.2) n (retargetTruth s truth')}
    MeasurableSet event ∧
      input.seededWorldLaw ν event =
        ν (B ∩ prefixSeedGate input C mode accounting rule tapes n s) *
          ∏ i, (input.experiment i).priorMass (truth' i) * ENNReal.ofReal
            ((input.experiment i).wordProbability (truth' i)
              (historyObservationWord input s.history i
                (prefix_historyObservation_alphabet input C mode accounting rule anchor truth tapes hp i))) := by
  have hvalid := prefix_historyObservation_alphabet input C mode accounting rule anchor truth tapes hp
  dsimp only
  rw [prefix_jointTruth_seedEvent_eq_rectangle input C hlate mode accounting rule anchor truth truth' tapes hp hf hvalid B]
  constructor
  · exact (hB.inter (measurableSet_prefixSeedGate input C mode accounting rule hm hlegal tapes n s
      (prefix_clock input C mode accounting rule anchor truth tapes hp))).prod
      (measurableSet_worldWordCylinder input truth' _)
  · rw [StatisticalInput.seededWorldLaw, Measure.prod_prod, worldLaw_worldWordCylinder]

end PaperProofs.Common.Native
