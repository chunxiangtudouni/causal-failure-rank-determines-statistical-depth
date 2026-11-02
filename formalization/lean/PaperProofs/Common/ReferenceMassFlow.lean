module

public import PaperProofs.Common.ReferenceEntryFlow
public import PaperProofs.Statistics.ReferenceBudgetMass
public import PaperProofs.Statistics.ReferenceBudgetMassTelescope

/-!
The original ideal-reference risk theorem. Actual ordinary errors are traced
back to real write actions before using the genuine entry-SPRT error bound.
Countable entry-atom integration and the original branch budgets prove the
actual stage-mass recursion. A finite positive-term ENNReal telescope then
proves ReferenceRiskGuarantee, retaining None, failed paths and terminal cases.
No risk, alignment or stopping conclusion is stored in a Policy or assumed;
no finite-cost/integrability premise or toReal conversion is used. Observation
cost asymptotics and the concrete selected-controller H0 qualification remain
separate obligations.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

private theorem written_frame (C : Contract I) (s : State I) (stage current : I.Stage) (bit : Bool)
    (hne : stage ≠ current) : (reportedWriteLedger C s current bit).written stage = s.ledger.written stage := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> simp only [writeLedger, Function.update_of_ne hne]

/-- A written ordinary bit is never overwritten by a later actual action. -/
theorem step_written_some (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next)
    (stage : I.Stage) (bit : Bool) (hw : s.ledger.written stage = some bit) :
    next.ledger.written stage = some bit := by
  cases hs with
  | review | allocate | execute | advance | stop | abandon => exact hw
  | write current newBit live port resources =>
    have hne : stage ≠ current := by intro h; subst stage; rw [port] at hw; cases hw
    simpa only [record, written_frame C s stage current newBit hne] using hw

/-- Any bit found in an actual Prefix has a genuine earlier policy write.
This does not select successful paths and does not replace non-MAP decisions. -/
theorem prefix_written_has_write {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (stage : I.Stage) (bit : Bool) (hw : s.ledger.written stage = some bit) :
    ∃ (m : ℕ) (old : State I), m < n ∧ Prefix input C mode accounting rule seed truth tapes m old ∧
      old.halted = false ∧ rule seed old.history = .write stage bit := by
  induction hp with
  | initial => cases hw
  | @next n s next earlier step ih =>
    generalize ha : rule seed s.history = action at step
    cases step with
    | write current newBit live port resources =>
      by_cases heq : stage = current
      · subst current
        have he : newBit = bit := by
          change (reportedWriteLedger C s stage newBit).written stage = some bit at hw
          have hnew : (reportedWriteLedger C s stage newBit).written stage = some newBit := by
            classical
            simp only [reportedWriteLedger]
            split_ifs <;> simp only [writeLedger, Function.update_self]
          exact Option.some.inj (hnew.symm.trans hw)
        subst newBit
        exact ⟨n, s, Nat.lt_succ_self n, earlier, live.1, ha⟩
      · have hwold : s.ledger.written stage = some bit := by
          simpa only [record, written_frame C s stage current newBit heq] using hw
        obtain ⟨m, old, hmn, hpold, hactive, hwrite⟩ := ih hwold
        exact ⟨m, old, hmn.trans (Nat.lt_succ_self n), hpold, hactive, hwrite⟩
    | review | allocate | execute | advance | stop | abandon =>
      obtain ⟨m, old, hmn, hpold, hactive, hwrite⟩ := ih hw
      exact ⟨m, old, hmn.trans (Nat.lt_succ_self n), hpold, hactive, hwrite⟩

private theorem prefix_eq_run_sample {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (sample : Seed × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) n s) : run input C .uncapped accounting rule sample n = s := by
  have he := prefix_eq_run input C .uncapped accounting rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hw : replayWorld input (input.truthAt sample.2) (worldTapes input sample.2) = sample.2 := rfl
  simpa only [hw] using he

/-- The original run has at some time an actually wrong ordinary bit.
Repairs never modify this event or rewrite the ordinary ledger. -/
def referenceStageWriteError (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    Set (Unit × input.World) :=
  {sample | ∃ n : ℕ,
    let s := run input C .uncapped accounting (referenceRule input available budget none) sample n
    s.ledger.written stage = some (!s.ledger.truth stage)}

theorem measurableSet_referenceStageWriteError (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    MeasurableSet (referenceStageWriteError input C accounting available budget stage) := by
  have heq : referenceStageWriteError input C accounting available budget stage =
      ⋃ n : ℕ, {sample : Unit × input.World |
        let s := run input C .uncapped accounting (referenceRule input available budget none) sample n
        s.ledger.written stage = some (!s.ledger.truth stage)} := by
    ext sample
    simp only [referenceStageWriteError, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_run input C .uncapped accounting (referenceRule (Seed := Unit) input available budget none)
    (measurable_referenceRule input available budget none) n)
    (MeasurableSpace.measurableSet_top (s := {s : State I | s.ledger.written stage = some (!s.ledger.truth stage)}))

/-- On a finite-target entry, any actual wrong ordinary bit belongs to the
same genuine posterior-write error event already bounded by the entry kernel. -/
theorem referenceStageWriteError_on_entry_subset
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (stage : I.Stage) (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : referenceAvailableEntryTarget input available budget history = some p) :
    referenceStageWriteError input C accounting available budget stage ∩
        {sample | entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history} ⊆
      referenceStagePosteriorError input C hearly accounting available budget stage ∩
        {sample | entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history} := by
  rintro ⟨⟨⟩, world⟩ ⟨⟨n, hw⟩, hentry⟩
  have hlegal := referenceRule_uncapped_legal (Seed := Unit) input C hearly accounting available budget none
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (referenceRule input available budget none) hlegal ((), world) n
  obtain ⟨m, old, _, hpold, hactive, hwrite⟩ := prefix_written_has_write input C .uncapped accounting
    (referenceRule input available budget none) () (input.truthAt world) (worldTapes input world) hp stage _ hw
  have ht := congrFun (run_truth input C .uncapped accounting (referenceRule input available budget none) hlegal ((), world) n) stage
  have hwrong : (!(run input C .uncapped accounting (referenceRule input available budget none) ((), world) n).ledger.truth stage) ≠
      (world stage).1 := by
    rw [ht]
    exact Bool.not_ne_self _
  refine ⟨⟨m, (!(run input C .uncapped accounting (referenceRule input available budget none) ((), world) n).ledger.truth stage), history, p, ?_⟩, hentry⟩
  dsimp only [referenceIdealPolicy, referenceUncappedPolicy]
  rw [prefix_eq_run_sample input C accounting (referenceRule input available budget none) ((), world) hpold]
  exact ⟨hactive, hwrite, hentry, htarget, hwrong⟩

theorem referenceStageWriteError_on_entry_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : referenceAvailableEntryTarget input available budget history = some p) :
    input.seededWorldLaw (Measure.dirac ())
      (referenceStageWriteError input C accounting available budget stage ∩
        {sample | entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history}) ≤
      ENNReal.ofReal (p : ℝ) * input.seededWorldLaw (Measure.dirac ())
        {sample | entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history} :=
  (measure_mono (referenceStageWriteError_on_entry_subset input C hearly accounting available budget stage history p htarget)).trans
    (referenceStagePosteriorError_on_entry_le input C hearly accounting available budget hbudget hsmall stage history p htarget)

private theorem prefix_early_written_reported {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (stage : I.Stage) (hw : s.ledger.written stage ≠ none) : s.ledger.reportTime stage ≠ none := by
  induction hp with
  | initial => exact (hw rfl).elim
  | @next n s next earlier step ih =>
    generalize ha : rule seed s.history = action at step
    cases step with
    | write current bit live port resources =>
      by_cases heq : stage = current
      · subst current
        simp only [record, reportedWriteLedger, hearly, ite_true, writeLedger, Function.update_self]
        simp
      · have hwold : s.ledger.written stage ≠ none := by
          simpa only [record, written_frame C s stage current bit heq] using hw
        simpa only [record, reportedWriteLedger, hearly, ite_true, writeLedger, Function.update_of_ne heq] using ih hwold
    | review | allocate | execute | advance | stop | abandon => exact ih hw

private theorem prefix_wrong_of_replayCorrect_false {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting rule seed truth tapes n s)
    (cache : ReferenceReplayCache I) (hseen : cache.seen = s.history) (stage : I.Stage)
    (hw : s.ledger.written stage ≠ none) (hcorrect : referenceReplayCorrect cache stage = false) :
    s.ledger.written stage = some (!s.ledger.truth stage) := by
  obtain ⟨bit, hwrite, hreport, hb⟩ := prefix_written_report_packet input C hearly .uncapped accounting
    rule seed truth tapes hp stage hw (prefix_early_written_reported input C hearly .uncapped accounting rule seed truth tapes hp stage hw)
  have hn : bit ≠ s.ledger.truth stage := by
    intro heq
    simp [referenceReplayCorrect, hseen, hwrite, hreport, heq] at hcorrect
  exact hb.trans (congrArg some (Bool.eq_not_iff.mpr hn))

/-- The original budget at an actual entry, zero on histories never entered. -/
noncomputable def referenceEntryBudgetPotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (sample : Unit × input.World) : ℝ≥0∞ :=
  match entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample with
  | none => 0
  | some history => ENNReal.ofReal ((referenceAvailableEntryRisk input available budget history).getD 0 : ℝ)

theorem measurable_referenceEntryBudgetPotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    Measurable (referenceEntryBudgetPotential input C accounting available budget stage) := by
  exact (measurable_of_countable (fun entry : EntryHistory I => match entry with
      | none => (0 : ℝ≥0∞)
      | some history => ENNReal.ofReal ((referenceAvailableEntryRisk input available budget history).getD 0 : ℝ))).comp
    (measurable_entryHistory input C .uncapped accounting (referenceRule (Seed := Unit) input available budget none)
      (measurable_referenceRule input available budget none) stage)

theorem referenceEntryBudgetPotential_le_quarter
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) (sample : Unit × input.World) :
    referenceEntryBudgetPotential input C accounting available budget stage sample ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  cases he : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample with
  | none => simp [referenceEntryBudgetPotential, he]
  | some history =>
    obtain ⟨kind, risk, _, hr, hv, _⟩ := referenceEntryRisk_kind_target input C hearly accounting available budget hbudget hsmall sample stage history he
    simp only [referenceEntryBudgetPotential, he, hr, Option.getD_some]
    apply ENNReal.ofReal_le_ofReal
    have hh : risk ≤ (1 / 4 : ℚ) := hv.2
    have hcast : (risk : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hh
    norm_num at hcast
    exact hcast

/-- Pull a genuine next entry back to its actual predecessor entry, retaining
the exact original branch budget and the real ordinary-error event. -/
theorem referenceNextEntry_budget_branch
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage nextStage : I.Stage)
    (hnextStage : nextStage.val = stage.val + 1)
    (history : List (VisibleEvent I)) (kind : ReferenceBudgetCase) (risk : ℚ)
    (hkind : referenceAvailableEntryKind input available budget history = some kind)
    (hrisk : referenceAvailableEntryRisk input available budget history = some risk)
    (sample : Unit × input.World)
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history)
    (nextHistory : List (VisibleEvent I))
    (hnext : entryHistory input C .uncapped accounting (referenceRule input available budget none) nextStage sample = some nextHistory) :
    ∃ (error : Bool) (childRisk : ℚ), ReferenceBudgetValid childRisk ∧
      referenceAvailableEntryRisk input available budget nextHistory = some childRisk ∧
      some childRisk = referenceBudgetStep kind error risk ∧
      (error = true → sample ∈ referenceStageWriteError input C accounting available budget stage) := by
  obtain ⟨n, s, next, hp, hrun, hs, ha, hhistory⟩ := referenceNextEntry_has_advance input C hearly accounting available budget
    sample stage nextStage hnextStage nextHistory hnext
  obtain ⟨cache, oldHistory, oldKind, oldRisk, haligned, hentry', _, hk, hr, _, hupdate⟩ :=
    referenceAdvance_entry_budget input C hearly accounting available budget hbudget hsmall sample hp stage nextStage hnextStage hs ha
  have heq : oldHistory = history := Option.some.inj (hentry'.symm.trans hentry)
  subst oldHistory
  have hkeq : oldKind = kind := Option.some.inj (hk.symm.trans hkind)
  have hreq : oldRisk = risk := Option.some.inj (hr.symm.trans hrisk)
  subst oldKind
  subst oldRisk
  obtain ⟨_, childRisk, _, hchild, hv, _⟩ := referenceEntryRisk_kind_target input C hearly accounting available budget
    hbudget hsmall sample nextStage nextHistory hnext
  rw [hhistory] at hupdate
  refine ⟨!(referenceReplayCorrect cache stage), childRisk, hv, hchild, hchild.symm.trans hupdate, ?_⟩
  intro herr
  have hc : referenceReplayCorrect cache stage = false := by
    cases hh : referenceReplayCorrect cache stage <;> simp_all
  have hw : s.ledger.written stage ≠ none := by cases hs with | advance _ _ written _ => exact written
  have hwrong := prefix_wrong_of_replayCorrect_false input C hearly accounting (referenceRule input available budget none)
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp cache haligned.seen stage hw hc
  refine ⟨n, ?_⟩
  rw [hrun]
  exact hwrong

private theorem entryKind_eq_cache {Seed : Type*}
    {input : StatisticalInput I} {C : Contract I} {accounting : NormalAccounting I}
    {available : Finset I.Tool} {budget : ℚ} {sample : Seed × input.World}
    {cache entry : ReferenceReplayCache I} {stage : I.Stage} {s : State I}
    (haligned : ReferenceStateAligned input available budget cache s) (hcursor : s.cursor = stage.val)
    (horigin : ReferenceEntryBudgetTrace input C accounting available budget sample cache entry stage) :
    referenceAvailableEntryKind input available budget cache.entryHistory = referenceAvailableKind I available cache := by
  simp only [referenceAvailableEntryKind, horigin.parsed_entry, Option.bind_eq_bind, Option.bind_some]
  have hc : historyCursor cache.seen = historyCursor entry.seen :=
    (haligned.cursor.trans hcursor).trans horigin.entry_cursor.symm
  simp only [referenceAvailableKind, referenceReplayStage, hc, horigin.entry_snapshot]

/-- A real no-tool failure is an ordinary error on a real entry whose
history-only original kind is exactly noTool. -/
theorem referenceNoToolFailure_entry_kind
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) (sample : Unit × input.World)
    (hfailure : sample ∈ referenceStageNoToolFailure input C accounting available budget stage) :
    ∃ history, entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history ∧
      referenceAvailableEntryKind input available budget history = some .noTool ∧
      sample ∈ referenceStageWriteError input C accounting available budget stage := by
  obtain ⟨n, cache, hactive, hcursor, _, hparse, _, _, hkind, hwrong⟩ := hfailure
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (referenceRule input available budget none)
    (referenceRule_uncapped_legal input C hearly accounting available budget none) sample n
  obtain ⟨actual, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have heq : actual = cache := Option.some.inj (haligned.parsed.symm.trans hparse)
  subst actual
  obtain ⟨entry, horigin⟩ := prefix_referenceEntryBudgetTrace input C hearly accounting available budget hbudget hsmall
    sample hp cache haligned hactive stage hcursor
  exact ⟨cache.entryHistory, horigin.actual_entry,
    (entryKind_eq_cache haligned hcursor horigin).trans hkind, n, hwrong⟩

theorem referenceNoToolFailure_on_entry_kind
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I)) :
    referenceStageNoToolFailure input C accounting available budget stage ∩
        {sample | entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history} ⊆
      {_sample | referenceAvailableEntryKind input available budget history = some .noTool} ∩
        (referenceStageWriteError input C accounting available budget stage ∩
          {sample | entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history}) := by
  intro sample hs
  obtain ⟨oldHistory, hentry, hkind, herror⟩ := referenceNoToolFailure_entry_kind input C hearly accounting available budget
    hbudget hsmall stage sample hs.1
  have heq : oldHistory = history := Option.some.inj (hentry.symm.trans hs.2)
  subst oldHistory
  exact ⟨hkind, herror, hs.2⟩

/-- Conditional on the current real entry, the next-entry budget is bounded
by these original branch weights. This is a pointwise execution theorem;
its error indicator is the actual ordinary-error event bounded above. -/
noncomputable def referenceChildBudgetEnvelope (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (risk : ℚ) (sample : Unit × input.World) : ℝ≥0∞ := by
  classical
  exact match kind with
  | .infiniteRank => ENNReal.ofReal (risk : ℝ)
  | .noTool => ENNReal.ofReal ((risk / 2 : ℚ) : ℝ)
  | .finiteBad depth => ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) +
      (referenceStageWriteError input C accounting available budget stage).indicator
        (fun _ => ENNReal.ofReal ((controllerBadRisk risk (controllerTarget risk depth.val) : ℚ) : ℝ)) sample

theorem referenceNextEntryBudget_le_on_entry
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage nextStage : I.Stage)
    (hnextStage : nextStage.val = stage.val + 1)
    (history : List (VisibleEvent I)) (kind : ReferenceBudgetCase) (risk : ℚ)
    (hkind : referenceAvailableEntryKind input available budget history = some kind)
    (hrisk : referenceAvailableEntryRisk input available budget history = some risk)
    (sample : Unit × input.World)
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history) :
    referenceEntryBudgetPotential input C accounting available budget nextStage sample ≤
      referenceChildBudgetEnvelope input C accounting available budget stage kind risk sample := by
  classical
  cases he : entryHistory input C .uncapped accounting (referenceRule input available budget none) nextStage sample with
  | none => simp [referenceEntryBudgetPotential, he]
  | some nextHistory =>
    obtain ⟨error, child, _, hc, hu, herr⟩ := referenceNextEntry_budget_branch input C hearly accounting available budget
      hbudget hsmall stage nextStage hnextStage history kind risk hkind hrisk sample hentry nextHistory he
    simp only [referenceEntryBudgetPotential, he, hc, Option.getD_some]
    cases kind with
    | infiniteRank =>
      have hchild : child = risk := Option.some.inj hu
      subst child
      exact le_rfl
    | noTool =>
      cases error with
      | false =>
        have hchild : child = risk / 2 := Option.some.inj hu
        subst child
        exact le_rfl
      | true => cases hu
    | finiteBad depth =>
      cases error with
      | false =>
        have hchild : child = risk / 2 := Option.some.inj hu
        subst child
        exact le_add_of_nonneg_right zero_le
      | true =>
        have hchild : child = controllerBadRisk risk (controllerTarget risk depth.val) := Option.some.inj hu
        subst child
        simp only [referenceChildBudgetEnvelope, Set.indicator_of_mem (herr rfl)]
        exact le_add_of_nonneg_left zero_le

/-- One atom of the genuine first-entry record; None has no budget mass. -/
def referenceEntryEvent (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (history : List (VisibleEvent I)) : Set (Unit × input.World) :=
  {sample | entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history}

theorem measurableSet_referenceEntryEvent (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (history : List (VisibleEvent I)) : MeasurableSet (referenceEntryEvent input C accounting available budget stage history) :=
  (measurable_entryHistory input C .uncapped accounting (referenceRule (Seed := Unit) input available budget none)
    (measurable_referenceRule input available budget none) stage) (measurableSet_singleton (some history))

private theorem noToolFailure_entry_empty
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I))
    (hkind : referenceAvailableEntryKind input available budget history ≠ some .noTool) :
    referenceStageNoToolFailure input C accounting available budget stage ∩
      referenceEntryEvent input C accounting available budget stage history = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro sample hs
  exact hkind ((referenceNoToolFailure_on_entry_kind input C hearly accounting available budget hbudget hsmall stage history hs).1)

/-- The real weighted mass inequality on every current-entry atom. It
includes null/malformed histories and retains actual no-tool failure mass.
The scalar branch bounds are instantiated with the original controller
targets and child risks; no mass-transfer or risk hypothesis is supplied. -/
theorem referenceBudgetMass_on_entry
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage nextStage : I.Stage)
    (hnextStage : nextStage.val = stage.val + 1) (history : List (VisibleEvent I)) :
    input.seededWorldLaw (Measure.dirac ())
        (referenceStageNoToolFailure input C accounting available budget stage ∩
          referenceEntryEvent input C accounting available budget stage history) +
      (∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
        referenceEntryBudgetPotential input C accounting available budget nextStage sample
          ∂input.seededWorldLaw (Measure.dirac ())) ≤
      ENNReal.ofReal ((referenceAvailableEntryRisk input available budget history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) := by
  classical
  let μ := input.seededWorldLaw (Measure.dirac ())
  let E := referenceEntryEvent input C accounting available budget stage history
  have hE : MeasurableSet E := measurableSet_referenceEntryEvent input C accounting available budget stage history
  by_cases hex : ∃ sample : Unit × input.World, sample ∈ E
  · obtain ⟨witness, hw⟩ := hex
    obtain ⟨kind, risk, hk, hr, hv, ht⟩ := referenceEntryRisk_kind_target input C hearly accounting available budget
      hbudget hsmall witness stage history hw
    have hi : (∫⁻ sample in E, referenceEntryBudgetPotential input C accounting available budget nextStage sample ∂μ) ≤
        ∫⁻ sample in E, referenceChildBudgetEnvelope input C accounting available budget stage kind risk sample ∂μ := by
      apply setLIntegral_mono' hE
      intro sample hs
      exact referenceNextEntryBudget_le_on_entry input C hearly accounting available budget hbudget hsmall stage nextStage
        hnextStage history kind risk hk hr sample hs
    change μ (referenceStageNoToolFailure input C accounting available budget stage ∩ E) +
      (∫⁻ sample in E, referenceEntryBudgetPotential input C accounting available budget nextStage sample ∂μ) ≤
        ENNReal.ofReal ((referenceAvailableEntryRisk input available budget history).getD 0 : ℝ) * μ E
    rw [hr, Option.getD_some]
    cases kind with
    | infiniteRank =>
      have hzero : μ (referenceStageNoToolFailure input C accounting available budget stage ∩ E) = 0 := by
        rw [show referenceStageNoToolFailure input C accounting available budget stage ∩ E = ∅ from
          noToolFailure_entry_empty input C hearly accounting available budget hbudget hsmall stage history (by rw [hk]; simp)]
        exact measure_empty
      rw [hzero, zero_add]
      simpa only [referenceChildBudgetEnvelope, setLIntegral_const] using hi
    | noTool =>
      have he : μ (referenceStageWriteError input C accounting available budget stage ∩ E) ≤
          ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E :=
        referenceStageWriteError_on_entry_le input C hearly accounting available budget hbudget hsmall stage history (risk / 2) ht
      have hf : μ (referenceStageNoToolFailure input C accounting available budget stage ∩ E) ≤
          μ (referenceStageWriteError input C accounting available budget stage ∩ E) :=
        measure_mono (fun sample hs => (referenceNoToolFailure_on_entry_kind input C hearly accounting available budget hbudget hsmall stage history hs).2)
      have hchild : (∫⁻ sample in E, referenceEntryBudgetPotential input C accounting available budget nextStage sample ∂μ) ≤
          ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E := by
        simpa only [referenceChildBudgetEnvelope, setLIntegral_const] using hi
      calc
        _ ≤ μ (referenceStageWriteError input C accounting available budget stage ∩ E) +
            ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E := add_le_add hf hchild
        _ = ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E +
            μ (referenceStageWriteError input C accounting available budget stage ∩ E) := add_comm _ _
        _ ≤ _ := referenceBudget_noTool_entry_mass risk hv.1.le _ _ he
    | finiteBad depth =>
      have hzero : μ (referenceStageNoToolFailure input C accounting available budget stage ∩ E) = 0 := by
        rw [show referenceStageNoToolFailure input C accounting available budget stage ∩ E = ∅ from
          noToolFailure_entry_empty input C hearly accounting available budget hbudget hsmall stage history (by rw [hk]; simp)]
        exact measure_empty
      rw [hzero, zero_add]
      have he : μ (referenceStageWriteError input C accounting available budget stage ∩ E) ≤
          ENNReal.ofReal ((controllerTarget risk depth.val : ℚ) : ℝ) * μ E :=
        referenceStageWriteError_on_entry_le input C hearly accounting available budget hbudget hsmall stage history _ ht
      have herror := measurableSet_referenceStageWriteError input C accounting available budget stage
      have heval : (∫⁻ sample in E, referenceChildBudgetEnvelope input C accounting available budget stage (.finiteBad depth) risk sample ∂μ) =
          ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E +
            ENNReal.ofReal ((controllerBadRisk risk (controllerTarget risk depth.val) : ℚ) : ℝ) *
              μ (referenceStageWriteError input C accounting available budget stage ∩ E) := by
        simp only [referenceChildBudgetEnvelope]
        rw [lintegral_add_right _ (measurable_const.indicator herror), setLIntegral_const,
          lintegral_indicator herror, setLIntegral_const, Measure.restrict_apply herror]
      exact (hi.trans_eq heval).trans (referenceBudget_finiteBad_entry_mass risk hv depth _ _ he)
  · have hEmpty : E = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun sample hs => hex ⟨sample, hs⟩)
    change μ (referenceStageNoToolFailure input C accounting available budget stage ∩ E) +
      (∫⁻ sample in E, referenceEntryBudgetPotential input C accounting available budget nextStage sample ∂μ) ≤ _
    rw [hEmpty]
    simp

/-- The next-stage budget is zero at the final stage. This is analysis of
the same actual entry selector, not an added terminal operation. -/
noncomputable def referenceNextBudgetPotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (sample : Unit × input.World) : ℝ≥0∞ :=
  if h : stage.val + 1 < I.stageCount then
    referenceEntryBudgetPotential input C accounting available budget ⟨stage.val + 1, h⟩ sample else 0

theorem measurable_referenceNextBudgetPotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    Measurable (referenceNextBudgetPotential input C accounting available budget stage) := by
  unfold referenceNextBudgetPotential
  split_ifs
  · exact measurable_referenceEntryBudgetPotential input C accounting available budget _
  · exact measurable_const

private theorem failureMass_on_entry
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) (history : List (VisibleEvent I)) :
    input.seededWorldLaw (Measure.dirac ())
      (referenceStageNoToolFailure input C accounting available budget stage ∩
        referenceEntryEvent input C accounting available budget stage history) ≤
      ENNReal.ofReal ((referenceAvailableEntryRisk input available budget history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) := by
  classical
  let μ := input.seededWorldLaw (Measure.dirac ())
  let E := referenceEntryEvent input C accounting available budget stage history
  by_cases hex : ∃ sample : Unit × input.World, sample ∈ E
  · obtain ⟨sample, hs⟩ := hex
    obtain ⟨kind, risk, hk, hr, hv, ht⟩ := referenceEntryRisk_kind_target input C hearly accounting available budget
      hbudget hsmall sample stage history hs
    rw [hr, Option.getD_some]
    cases kind with
    | infiniteRank | finiteBad depth =>
      rw [noToolFailure_entry_empty input C hearly accounting available budget hbudget hsmall stage history (by rw [hk]; simp)]
      simp
    | noTool =>
      have he := referenceStageWriteError_on_entry_le input C hearly accounting available budget hbudget hsmall stage history (risk / 2) ht
      calc
        _ ≤ μ (referenceStageWriteError input C accounting available budget stage ∩ E) :=
          measure_mono (fun sample hs => (referenceNoToolFailure_on_entry_kind input C hearly accounting available budget hbudget hsmall stage history hs).2)
        _ ≤ ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E +
            μ (referenceStageWriteError input C accounting available budget stage ∩ E) := le_add_of_nonneg_left zero_le
        _ ≤ _ := referenceBudget_noTool_entry_mass risk hv.1.le _ _ he
  · have hEmpty : E = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun sample hs => hex ⟨sample, hs⟩)
    change μ (_ ∩ E) ≤ _ * μ E
    rw [hEmpty]
    simp

theorem referenceBudgetMass_on_entry_allStages
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) (history : List (VisibleEvent I)) :
    input.seededWorldLaw (Measure.dirac ())
        (referenceStageNoToolFailure input C accounting available budget stage ∩
          referenceEntryEvent input C accounting available budget stage history) +
      (∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
        referenceNextBudgetPotential input C accounting available budget stage sample
          ∂input.seededWorldLaw (Measure.dirac ())) ≤
      ENNReal.ofReal ((referenceAvailableEntryRisk input available budget history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) := by
  unfold referenceNextBudgetPotential
  split_ifs with hnext
  · exact referenceBudgetMass_on_entry input C hearly accounting available budget hbudget hsmall
      stage ⟨stage.val + 1, hnext⟩ rfl history
  · simpa only [lintegral_zero, add_zero] using failureMass_on_entry input C hearly accounting available budget hbudget hsmall stage history

theorem measurableSet_referenceStageNoToolFailure (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    MeasurableSet (referenceStageNoToolFailure input C accounting available budget stage) := by
  have heq : referenceStageNoToolFailure input C accounting available budget stage =
      ⋃ n : ℕ, (run input C .uncapped accounting (referenceRule (Seed := Unit) input available budget none) · n) ⁻¹'
        {s : State I | ∃ cache : ReferenceReplayCache I,
          s.halted = false ∧ s.cursor = stage.val ∧
            referenceRule input available budget none () s.history = .abandon ∧
            referenceAvailableReplay input available budget s.history = some cache ∧ cache.phase = .reported ∧
            referenceReplayCorrect cache stage = false ∧ referenceAvailableKind I available cache = some .noTool ∧
            s.ledger.written stage = some (!s.ledger.truth stage)} := by
    ext sample
    have hunit : sample.1 = () := Subsingleton.elim _ _
    simp only [referenceStageNoToolFailure, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, hunit]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_run input C .uncapped accounting (referenceRule input available budget none)
    (measurable_referenceRule input available budget none) n) MeasurableSpace.measurableSet_top

/-- Exact countable entry-atom integration, with no conditioning kernel or
point-mass assumption on the original private seed. -/
theorem lintegral_eq_tsum_referenceEntry
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (f : Unit × input.World → ℝ≥0∞) (hf : Measurable f)
    (hzero : ∀ sample, entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = none → f sample = 0) :
    (∫⁻ sample, f sample ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I), ∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
        f sample ∂input.seededWorldLaw (Measure.dirac ()) := by
  classical
  have hsplit : ∀ sample, f sample = ∑' history : List (VisibleEvent I),
      (referenceEntryEvent input C accounting available budget stage history).indicator f sample := by
    intro sample
    cases he : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample with
    | none =>
      rw [hzero sample he]
      symm
      calc
        _ = ∑' _history : List (VisibleEvent I), (0 : ℝ≥0∞) := by
          apply tsum_congr
          intro history
          apply Set.indicator_of_notMem
          intro hh
          have hnone := he.symm.trans hh
          cases hnone
        _ = 0 := tsum_zero
    | some history =>
      symm
      calc
        _ = (referenceEntryEvent input C accounting available budget stage history).indicator f sample := by
          apply tsum_eq_single history
          intro other hne
          apply Set.indicator_of_notMem
          intro hh
          exact hne (Option.some.inj (hh.symm.trans he))
        _ = f sample := Set.indicator_of_mem (show sample ∈ referenceEntryEvent input C accounting available budget stage history from he) f
  calc
    _ = ∫⁻ sample, ∑' history : List (VisibleEvent I),
        (referenceEntryEvent input C accounting available budget stage history).indicator f sample
          ∂input.seededWorldLaw (Measure.dirac ()) := lintegral_congr hsplit
    _ = ∑' history : List (VisibleEvent I), ∫⁻ sample,
        (referenceEntryEvent input C accounting available budget stage history).indicator f sample
          ∂input.seededWorldLaw (Measure.dirac ()) :=
      lintegral_tsum (fun history => (hf.indicator (measurableSet_referenceEntryEvent input C accounting available budget stage history)).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro history
      exact lintegral_indicator (measurableSet_referenceEntryEvent input C accounting available budget stage history) f

theorem referenceNextBudget_zero_of_no_entry
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) (sample : Unit × input.World)
    (hnone : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = none) :
    referenceNextBudgetPotential input C accounting available budget stage sample = 0 := by
  unfold referenceNextBudgetPotential
  split_ifs with hnext
  · cases he : entryHistory input C .uncapped accounting (referenceRule input available budget none) ⟨stage.val + 1, hnext⟩ sample with
    | none => simp [referenceEntryBudgetPotential, he]
    | some nextHistory =>
      obtain ⟨n, s, next, hp, _, hs, ha, _⟩ := referenceNextEntry_has_advance input C hearly accounting available budget
        sample stage ⟨stage.val + 1, hnext⟩ rfl nextHistory he
      obtain ⟨cache, history, kind, risk, _, hentry, _⟩ := referenceAdvance_entry_budget input C hearly accounting available budget
        hbudget hsmall sample hp stage ⟨stage.val + 1, hnext⟩ rfl hs ha
      rw [hnone] at hentry
      cases hentry
  · rfl

private theorem failureMass_eq_tsum_entry
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ()) (referenceStageNoToolFailure input C accounting available budget stage) =
      ∑' history : List (VisibleEvent I), input.seededWorldLaw (Measure.dirac ())
        (referenceStageNoToolFailure input C accounting available budget stage ∩
          referenceEntryEvent input C accounting available budget stage history) := by
  classical
  let F := referenceStageNoToolFailure input C accounting available budget stage
  have hF : MeasurableSet F := measurableSet_referenceStageNoToolFailure input C accounting available budget stage
  have hzero : ∀ sample : Unit × input.World,
      entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = none →
        F.indicator (fun _ => (1 : ℝ≥0∞)) sample = 0 := by
    intro sample hnone
    apply Set.indicator_of_notMem
    intro hs
    obtain ⟨history, hentry, _⟩ := referenceNoToolFailure_entry_kind input C hearly accounting available budget hbudget hsmall stage sample hs
    rw [hnone] at hentry
    cases hentry
  have hx := lintegral_eq_tsum_referenceEntry input C accounting available budget stage
    (F.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hF) hzero
  simpa only [lintegral_indicator_const hF, one_mul, Measure.restrict_apply hF] using hx

private theorem currentBudgetMass_eq_tsum_entry
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    (∫⁻ sample, referenceEntryBudgetPotential input C accounting available budget stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I), ENNReal.ofReal ((referenceAvailableEntryRisk input available budget history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) := by
  rw [lintegral_eq_tsum_referenceEntry input C accounting available budget stage _
    (measurable_referenceEntryBudgetPotential input C accounting available budget stage)
    (fun sample hs => by simp only [referenceEntryBudgetPotential, hs])]
  apply tsum_congr
  intro history
  calc
    _ = ∫⁻ _sample in referenceEntryEvent input C accounting available budget stage history,
        ENNReal.ofReal ((referenceAvailableEntryRisk input available budget history).getD 0 : ℝ)
          ∂input.seededWorldLaw (Measure.dirac ()) := by
      apply setLIntegral_congr_fun (measurableSet_referenceEntryEvent input C accounting available budget stage history)
      intro sample hs
      simp only [referenceEntryBudgetPotential, show entryHistory input C .uncapped accounting
        (referenceRule input available budget none) stage sample = some history from hs]
    _ = _ := setLIntegral_const _ _

/-- The true probability-weighted stage recursion. All current-entry atoms
are summed using the real record law; unentered histories contribute zero.
No eventual-success restriction, finite-cost premise or risk assumption occurs. -/
theorem referenceStage_budget_mass_nonincreasing
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ()) (referenceStageNoToolFailure input C accounting available budget stage) +
      (∫⁻ sample, referenceNextBudgetPotential input C accounting available budget stage sample
        ∂input.seededWorldLaw (Measure.dirac ())) ≤
      ∫⁻ sample, referenceEntryBudgetPotential input C accounting available budget stage sample
        ∂input.seededWorldLaw (Measure.dirac ()) := by
  have hnext := lintegral_eq_tsum_referenceEntry input C accounting available budget stage _
    (measurable_referenceNextBudgetPotential input C accounting available budget stage)
    (referenceNextBudget_zero_of_no_entry input C hearly accounting available budget hbudget hsmall stage)
  calc
    _ = (∑' history : List (VisibleEvent I), input.seededWorldLaw (Measure.dirac ())
          (referenceStageNoToolFailure input C accounting available budget stage ∩
            referenceEntryEvent input C accounting available budget stage history)) +
        (∑' history : List (VisibleEvent I), ∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
          referenceNextBudgetPotential input C accounting available budget stage sample ∂input.seededWorldLaw (Measure.dirac ())) := by
      rw [failureMass_eq_tsum_entry input C hearly accounting available budget hbudget hsmall stage, hnext]
    _ = ∑' history : List (VisibleEvent I),
        (input.seededWorldLaw (Measure.dirac ()) (referenceStageNoToolFailure input C accounting available budget stage ∩
          referenceEntryEvent input C accounting available budget stage history) +
          ∫⁻ sample in referenceEntryEvent input C accounting available budget stage history,
            referenceNextBudgetPotential input C accounting available budget stage sample ∂input.seededWorldLaw (Measure.dirac ())) := ENNReal.tsum_add.symm
    _ ≤ ∑' history : List (VisibleEvent I), ENNReal.ofReal ((referenceAvailableEntryRisk input available budget history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (referenceEntryEvent input C accounting available budget stage history) :=
      ENNReal.tsum_le_tsum (referenceBudgetMass_on_entry_allStages input C hearly accounting available budget hbudget hsmall stage)
    _ = _ := (currentBudgetMass_eq_tsum_entry input C accounting available budget stage).symm

/-- Budget mass before cursor k, with the terminal mass fixed to zero. -/
noncomputable def referenceBudgetMassAt (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (k : ℕ) : ℝ≥0∞ :=
  if h : k < I.stageCount then
    ∫⁻ sample, referenceEntryBudgetPotential input C accounting available budget ⟨k, h⟩ sample
      ∂input.seededWorldLaw (Measure.dirac ()) else 0

noncomputable def referenceFailureMassAt (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (k : ℕ) : ℝ≥0∞ :=
  if h : k < I.stageCount then
    input.seededWorldLaw (Measure.dirac ()) (referenceStageNoToolFailure input C accounting available budget ⟨k, h⟩) else 0

theorem referenceBudgetMassAt_step
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (k : ℕ) (hk : k < I.stageCount) :
    referenceFailureMassAt input C accounting available budget k + referenceBudgetMassAt input C accounting available budget (k + 1) ≤
      referenceBudgetMassAt input C accounting available budget k := by
  have hn : referenceBudgetMassAt input C accounting available budget (k + 1) =
      ∫⁻ sample, referenceNextBudgetPotential input C accounting available budget ⟨k, hk⟩ sample
        ∂input.seededWorldLaw (Measure.dirac ()) := by
    by_cases hnext : k + 1 < I.stageCount <;>
      simp only [referenceBudgetMassAt, referenceNextBudgetPotential, hnext, ↓reduceDIte, lintegral_zero]
  rw [hn]
  simp only [referenceFailureMassAt, referenceBudgetMassAt, hk, dite_true]
  exact referenceStage_budget_mass_nonincreasing input C hearly accounting available budget hbudget hsmall ⟨k, hk⟩

theorem referenceBudgetMassAt_terminal (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) :
    referenceBudgetMassAt input C accounting available budget I.stageCount = 0 := by
  simp only [referenceBudgetMassAt, lt_self_iff_false, dite_false]

/-- The actual stage-zero record is [], so the initial budget mass is at
most the original budget/2 (zero for an empty task). -/
theorem referenceBudgetMassAt_initial
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    referenceBudgetMassAt input C accounting available budget 0 ≤ ENNReal.ofReal ((budget / 2 : ℚ) : ℝ) := by
  by_cases hzero : 0 < I.stageCount
  · simp only [referenceBudgetMassAt, hzero, dite_true]
    have hpoint : ∀ sample : Unit × input.World,
        referenceEntryBudgetPotential input C accounting available budget ⟨0, hzero⟩ sample =
          ENNReal.ofReal ((budget / 2 : ℚ) : ℝ) := by
      intro sample
      have he := entryHistory_stageZero input C .uncapped accounting (referenceRule (Seed := Unit) input available budget none)
        ⟨0, hzero⟩ rfl sample
      simp only [referenceEntryBudgetPotential, he, referenceAvailableEntryRisk_initial input available budget hbudget hsmall, Option.getD_some]
    calc
      _ = ∫⁻ _sample : Unit × input.World, ENNReal.ofReal ((budget / 2 : ℚ) : ℝ)
          ∂input.seededWorldLaw (Measure.dirac ()) := lintegral_congr hpoint
      _ ≤ ENNReal.ofReal ((budget / 2 : ℚ) : ℝ) := by simp
  · simp only [referenceBudgetMassAt, hzero, dite_false]
    exact zero_le

/-- The complete original ideal-reference risk bound. The actual failure
events are bounded by a finite positive-term budget telescope, after the
real entry-law mass recursion. Failed paths and unentered histories remain
in the original run measure; no risk/termination/alignment premise is added. -/
theorem referenceIdealRisk_le_half
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    risk input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      ENNReal.ofReal ((budget : ℝ) / 2) := by
  have hsum : (∑ stage : I.Stage, input.seededWorldLaw (Measure.dirac ())
      (referenceStageNoToolFailure input C accounting available budget stage)) =
      ∑ k ∈ Finset.range I.stageCount, referenceFailureMassAt input C accounting available budget k := by
    calc
      _ = ∑ stage : I.Stage, referenceFailureMassAt input C accounting available budget stage.val := by
        apply Finset.sum_congr rfl
        intro stage _
        unfold referenceFailureMassAt
        rw [dite_eq_left (show stage.val < I.stageCount from stage.isLt)]
      _ = _ := Fin.sum_univ_eq_sum_range _ I.stageCount
  calc
    _ ≤ ∑ stage : I.Stage, input.seededWorldLaw (Measure.dirac ())
        (referenceStageNoToolFailure input C accounting available budget stage) :=
      referenceRisk_le_sum_noToolFailure input C hearly accounting available budget hbudget hsmall
    _ = ∑ k ∈ Finset.range I.stageCount, referenceFailureMassAt input C accounting available budget k := hsum
    _ ≤ ENNReal.ofReal ((budget / 2 : ℚ) : ℝ) :=
      referenceFailureMass_sum_le_initial (referenceFailureMassAt input C accounting available budget)
        (referenceBudgetMassAt input C accounting available budget) I.stageCount _
        (referenceBudgetMassAt_step input C hearly accounting available budget hbudget hsmall)
        (referenceBudgetMassAt_initial input C accounting available budget hbudget hsmall)
    _ = _ := by
      congr 1
      push_cast
      rfl

/-- B17, instantiated on the original current-allocation contract. The
reference risk statement is now proved, rather than a performance field. -/
theorem referenceRiskGuarantee (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) : ReferenceRiskGuarantee input C accounting := by
  intro hcurrent available budget hbudget hsmall
  exact referenceIdealRisk_le_half input C hcurrent.1 accounting available budget hbudget hsmall

end PaperProofs.Common.Native
