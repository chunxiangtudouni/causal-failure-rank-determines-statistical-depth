module

public import PaperProofs.Common.PSTR_ST_TableEntry_012
public import PaperProofs.Common.ReferenceMassFlow

/-! Actual table ideal risk budget-mass induction. Real writes and genuine
entry histories feed the proved entry-SPRT error kernel; ENNReal mass flow
retains unentered histories, all failed paths and null entries. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.TableMass

open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice TableAlignment TableOrigin TableDecision TableInfinite TableTermination TableEntry

variable {I : Instance}

theorem measurable_tableRule (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (limit : ReferenceObservationLimit I) :
    MeasurableRule (tableRule input available budget limit) :=
  (measurable_of_countable (fun history => tableRule input available budget limit () history)).comp measurable_snd

private theorem written_frame (C : Contract I) (s : State I) (stage current : I.Stage) (bit : Bool)
    (hne : stage ≠ current) : (reportedWriteLedger C s current bit).written stage = s.ledger.written stage := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> simp only [writeLedger, Function.update_of_ne hne]

variable (hlaminar : LaminarSchedule I.compatibility)
include hlaminar

omit hlaminar in
private theorem prefix_eq_run_sample  (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Unit) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) n s) : run input C .uncapped accounting rule sample n = s := by
  have he := prefix_eq_run input C .uncapped accounting rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hw : replayWorld input (input.truthAt sample.2) (worldTapes input sample.2) = sample.2 := rfl
  simpa only [hw] using he

omit hlaminar in
/-- The original run has at some time an actually wrong ordinary bit.
Repairs never modify this event or rewrite the ordinary ledger. -/
def tableStageWriteError (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    Set (Unit × input.World) :=
  {sample | ∃ n : ℕ,
    let s := run input C .uncapped accounting (tableRule input available budget none) sample n
    s.ledger.written stage = some (!s.ledger.truth stage)}

omit hlaminar in
theorem measurableSet_tableStageWriteError (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    MeasurableSet (tableStageWriteError input C accounting available budget stage) := by
  have heq : tableStageWriteError input C accounting available budget stage =
      ⋃ n : ℕ, {sample : Unit × input.World |
        let s := run input C .uncapped accounting (tableRule input available budget none) sample n
        s.ledger.written stage = some (!s.ledger.truth stage)} := by
    ext sample
    simp only [tableStageWriteError, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_run input C .uncapped accounting (tableRule  input available budget none)
    (measurable_tableRule input available budget none) n)
    (MeasurableSpace.measurableSet_top (s := {s : State I | s.ledger.written stage = some (!s.ledger.truth stage)}))

omit hlaminar in
/-- On a finite-target entry, any actual wrong ordinary bit belongs to the
same genuine posterior-write error event already bounded by the entry kernel. -/
theorem tableStageWriteError_on_entry_subset
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (stage : I.Stage) (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : tableEntryTarget input available budget history = some p) :
    tableStageWriteError input C accounting available budget stage ∩
        {sample | entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history} ⊆
      tableStagePosteriorError input C hearly accounting available budget stage ∩
        {sample | entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history} := by
  rintro ⟨⟨⟩, world⟩ ⟨⟨n, hw⟩, hentry⟩
  have hlegal := tableRule_uncapped_legal  input C hearly accounting available budget none
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (tableRule input available budget none) hlegal ((), world) n
  obtain ⟨m, old, _, hpold, hactive, hwrite⟩ := prefix_written_has_write input C .uncapped accounting
    (tableRule input available budget none) () (input.truthAt world) (worldTapes input world) hp stage _ hw
  have ht := congrFun (run_truth input C .uncapped accounting (tableRule input available budget none) hlegal ((), world) n) stage
  have hwrong : (!(run input C .uncapped accounting (tableRule input available budget none) ((), world) n).ledger.truth stage) ≠
      (world stage).1 := by
    rw [ht]
    exact Bool.not_ne_self _
  refine ⟨⟨m, (!(run input C .uncapped accounting (tableRule input available budget none) ((), world) n).ledger.truth stage), history, p, ?_⟩, hentry⟩
  dsimp only [tableIdealPolicy, tableUncappedPolicy]
  rw [prefix_eq_run_sample input C accounting (tableRule input available budget none) ((), world) hpold]
  exact ⟨hactive, hwrite, hentry, htarget, hwrong⟩

theorem tableStageWriteError_on_entry_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : tableEntryTarget input available budget history = some p) :
    input.seededWorldLaw (Measure.dirac ())
      (tableStageWriteError input C accounting available budget stage ∩
        {sample | entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history}) ≤
      ENNReal.ofReal (p : ℝ) * input.seededWorldLaw (Measure.dirac ())
        {sample | entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history} :=
  (measure_mono (tableStageWriteError_on_entry_subset input C hearly accounting available budget stage history p htarget)).trans
    (tableStagePosteriorError_on_entry_le input hlaminar C hearly accounting available budget hbudget hsmall stage history p htarget)

omit hlaminar in
private theorem prefix_early_written_reported 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Unit)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
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

omit hlaminar in
private theorem prefix_wrong_of_replayCorrect_false 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (rule : PolicyRule I Unit)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
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

omit hlaminar in
/-- The original budget at an actual entry, zero on histories never entered. -/
noncomputable def tableEntryBudgetPotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (sample : Unit × input.World) : ℝ≥0∞ :=
  match entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample with
  | none => 0
  | some history => ENNReal.ofReal ((tableEntryRisk input available budget history).getD 0 : ℝ)

omit hlaminar in
theorem measurable_tableEntryBudgetPotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    Measurable (tableEntryBudgetPotential input C accounting available budget stage) := by
  exact (measurable_of_countable (fun entry : EntryHistory I => match entry with
      | none => (0 : ℝ≥0∞)
      | some history => ENNReal.ofReal ((tableEntryRisk input available budget history).getD 0 : ℝ))).comp
    (measurable_entryHistory input C .uncapped accounting (tableRule  input available budget none)
      (measurable_tableRule input available budget none) stage)

theorem tableEntryBudgetPotential_le_quarter
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) (sample : Unit × input.World) :
    tableEntryBudgetPotential input C accounting available budget stage sample ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  cases he : entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample with
  | none => simp [tableEntryBudgetPotential, he]
  | some history =>
    obtain ⟨kind, risk, _, hr, hv, _⟩ := tableEntryRisk_kind_target hlaminar input C hearly accounting available budget hbudget hsmall sample stage history he
    simp only [tableEntryBudgetPotential, he, hr, Option.getD_some]
    apply ENNReal.ofReal_le_ofReal
    have hh : risk ≤ (1 / 4 : ℚ) := hv.2
    have hcast : (risk : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hh
    norm_num at hcast
    exact hcast

/-- Pull a genuine next entry back to its actual predecessor entry, retaining
the exact original branch budget and the real ordinary-error event. -/
theorem tableNextEntry_budget_branch
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage nextStage : I.Stage)
    (hnextStage : nextStage.val = stage.val + 1)
    (history : List (VisibleEvent I)) (kind : ReferenceBudgetCase) (risk : ℚ)
    (hkind : tableEntryKind input available budget history = some kind)
    (hrisk : tableEntryRisk input available budget history = some risk)
    (sample : Unit × input.World)
    (hentry : entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history)
    (nextHistory : List (VisibleEvent I))
    (hnext : entryHistory input C .uncapped accounting (tableRule input available budget none) nextStage sample = some nextHistory) :
    ∃ (error : Bool) (childRisk : ℚ), ReferenceBudgetValid childRisk ∧
      tableEntryRisk input available budget nextHistory = some childRisk ∧
      some childRisk = referenceBudgetStep kind error risk ∧
      (error = true → sample ∈ tableStageWriteError input C accounting available budget stage) := by
  obtain ⟨n, s, next, hp, hrun, hs, ha, hhistory⟩ := tableNextEntry_has_advance input C hearly accounting available budget
    sample stage nextStage hnextStage nextHistory hnext
  obtain ⟨cache, oldHistory, oldKind, oldRisk, haligned, hentry', _, hk, hr, _, hupdate⟩ :=
    tableAdvance_entry_budget hlaminar input C hearly accounting available budget hbudget hsmall sample hp stage nextStage hnextStage hs ha
  have heq : oldHistory = history := Option.some.inj (hentry'.symm.trans hentry)
  subst oldHistory
  have hkeq : oldKind = kind := Option.some.inj (hk.symm.trans hkind)
  have hreq : oldRisk = risk := Option.some.inj (hr.symm.trans hrisk)
  subst oldKind
  subst oldRisk
  obtain ⟨_, childRisk, _, hchild, hv, _⟩ := tableEntryRisk_kind_target hlaminar input C hearly accounting available budget
    hbudget hsmall sample nextStage nextHistory hnext
  rw [hhistory] at hupdate
  refine ⟨!(referenceReplayCorrect cache stage), childRisk, hv, hchild, hchild.symm.trans hupdate, ?_⟩
  intro herr
  have hc : referenceReplayCorrect cache stage = false := by
    cases hh : referenceReplayCorrect cache stage <;> simp_all
  have hw : s.ledger.written stage ≠ none := by cases hs with | advance _ _ written _ => exact written
  have hwrong := prefix_wrong_of_replayCorrect_false input C hearly accounting (tableRule input available budget none)
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp cache haligned.seen stage hw hc
  refine ⟨n, ?_⟩
  rw [hrun]
  exact hwrong

omit hlaminar in
private theorem entryKind_eq_cache 
    {input : StatisticalInput I} {C : Contract I} {accounting : NormalAccounting I}
    {available : Finset I.Tool} {budget : ℚ} {sample : Unit × input.World}
    {cache entry : ReferenceReplayCache I} {stage : I.Stage} {s : State I}
    (haligned : TableStateAligned input available budget cache s) (hcursor : s.cursor = stage.val)
    (horigin : TableEntryBudgetTrace input C accounting available budget sample cache entry stage) :
    tableEntryKind input available budget cache.entryHistory = tableKind I available cache := by
  simp only [tableEntryKind, horigin.parsed_entry, Option.bind_eq_bind, Option.bind_some]
  have hc : historyCursor cache.seen = historyCursor entry.seen :=
    (haligned.cursor.trans hcursor).trans horigin.entry_cursor.symm
  simp only [tableKind, referenceReplayStage, hc, horigin.entry_snapshot]

/-- A real no-tool failure is an ordinary error on a real entry whose
history-only original kind is exactly noTool. -/
theorem tableNoToolFailure_entry_kind
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) (sample : Unit × input.World)
    (hfailure : sample ∈ tableStageNoToolFailure input C accounting available budget stage) :
    ∃ history, entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history ∧
      tableEntryKind input available budget history = some .noTool ∧
      sample ∈ tableStageWriteError input C accounting available budget stage := by
  obtain ⟨n, cache, hactive, hcursor, _, hparse, _, _, hkind, hwrong⟩ := hfailure
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (tableRule input available budget none)
    (tableRule_uncapped_legal input C hearly accounting available budget none) sample n
  obtain ⟨actual, haligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have heq : actual = cache := Option.some.inj (haligned.parsed.symm.trans hparse)
  subst actual
  obtain ⟨entry, horigin⟩ := prefix_tableEntryBudgetTrace hlaminar input C hearly accounting available budget hbudget hsmall
    sample hp cache haligned hactive stage hcursor
  exact ⟨cache.entryHistory, horigin.actual_entry,
    (entryKind_eq_cache haligned hcursor horigin).trans hkind, n, hwrong⟩

theorem tableNoToolFailure_on_entry_kind
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I)) :
    tableStageNoToolFailure input C accounting available budget stage ∩
        {sample | entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history} ⊆
      {_sample | tableEntryKind input available budget history = some .noTool} ∩
        (tableStageWriteError input C accounting available budget stage ∩
          {sample | entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history}) := by
  intro sample hs
  obtain ⟨oldHistory, hentry, hkind, herror⟩ := tableNoToolFailure_entry_kind hlaminar input C hearly accounting available budget
    hbudget hsmall stage sample hs.1
  have heq : oldHistory = history := Option.some.inj (hentry.symm.trans hs.2)
  subst oldHistory
  exact ⟨hkind, herror, hs.2⟩

omit hlaminar in
/-- Conditional on the current real entry, the next-entry budget is bounded
by these original branch weights. This is a pointwise execution theorem;
its error indicator is the actual ordinary-error event bounded above. -/
noncomputable def tableChildBudgetEnvelope (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (risk : ℚ) (sample : Unit × input.World) : ℝ≥0∞ := by
  classical
  exact match kind with
  | .infiniteRank => ENNReal.ofReal (risk : ℝ)
  | .noTool => ENNReal.ofReal ((risk / 2 : ℚ) : ℝ)
  | .finiteBad depth => ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) +
      (tableStageWriteError input C accounting available budget stage).indicator
        (fun _ => ENNReal.ofReal ((controllerBadRisk risk (controllerTarget risk depth.val) : ℚ) : ℝ)) sample

theorem tableNextEntryBudget_le_on_entry
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage nextStage : I.Stage)
    (hnextStage : nextStage.val = stage.val + 1)
    (history : List (VisibleEvent I)) (kind : ReferenceBudgetCase) (risk : ℚ)
    (hkind : tableEntryKind input available budget history = some kind)
    (hrisk : tableEntryRisk input available budget history = some risk)
    (sample : Unit × input.World)
    (hentry : entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history) :
    tableEntryBudgetPotential input C accounting available budget nextStage sample ≤
      tableChildBudgetEnvelope input C accounting available budget stage kind risk sample := by
  classical
  cases he : entryHistory input C .uncapped accounting (tableRule input available budget none) nextStage sample with
  | none => simp [tableEntryBudgetPotential, he]
  | some nextHistory =>
    obtain ⟨error, child, _, hc, hu, herr⟩ := tableNextEntry_budget_branch hlaminar input C hearly accounting available budget
      hbudget hsmall stage nextStage hnextStage history kind risk hkind hrisk sample hentry nextHistory he
    simp only [tableEntryBudgetPotential, he, hc, Option.getD_some]
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
        simp only [tableChildBudgetEnvelope, Set.indicator_of_mem (herr rfl)]
        exact le_add_of_nonneg_left zero_le

omit hlaminar in
/-- One atom of the genuine first-entry record; None has no budget mass. -/
def tableEntryEvent (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (history : List (VisibleEvent I)) : Set (Unit × input.World) :=
  {sample | entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history}

omit hlaminar in
theorem measurableSet_tableEntryEvent (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (history : List (VisibleEvent I)) : MeasurableSet (tableEntryEvent input C accounting available budget stage history) :=
  (measurable_entryHistory input C .uncapped accounting (tableRule  input available budget none)
    (measurable_tableRule input available budget none) stage) (measurableSet_singleton (some history))

private theorem noToolFailure_entry_empty
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I))
    (hkind : tableEntryKind input available budget history ≠ some .noTool) :
    tableStageNoToolFailure input C accounting available budget stage ∩
      tableEntryEvent input C accounting available budget stage history = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro sample hs
  exact hkind ((tableNoToolFailure_on_entry_kind hlaminar input C hearly accounting available budget hbudget hsmall stage history hs).1)

/-- The real weighted mass inequality on every current-entry atom. It
includes null/malformed histories and retains actual no-tool failure mass.
The scalar branch bounds are instantiated with the original controller
targets and child risks; no mass-transfer or risk hypothesis is supplied. -/
theorem tableBudgetMass_on_entry
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage nextStage : I.Stage)
    (hnextStage : nextStage.val = stage.val + 1) (history : List (VisibleEvent I)) :
    input.seededWorldLaw (Measure.dirac ())
        (tableStageNoToolFailure input C accounting available budget stage ∩
          tableEntryEvent input C accounting available budget stage history) +
      (∫⁻ sample in tableEntryEvent input C accounting available budget stage history,
        tableEntryBudgetPotential input C accounting available budget nextStage sample
          ∂input.seededWorldLaw (Measure.dirac ())) ≤
      ENNReal.ofReal ((tableEntryRisk input available budget history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (tableEntryEvent input C accounting available budget stage history) := by
  classical
  let μ := input.seededWorldLaw (Measure.dirac ())
  let E := tableEntryEvent input C accounting available budget stage history
  have hE : MeasurableSet E := measurableSet_tableEntryEvent input C accounting available budget stage history
  by_cases hex : ∃ sample : Unit × input.World, sample ∈ E
  · obtain ⟨witness, hw⟩ := hex
    obtain ⟨kind, risk, hk, hr, hv, ht⟩ := tableEntryRisk_kind_target hlaminar input C hearly accounting available budget
      hbudget hsmall witness stage history hw
    have hi : (∫⁻ sample in E, tableEntryBudgetPotential input C accounting available budget nextStage sample ∂μ) ≤
        ∫⁻ sample in E, tableChildBudgetEnvelope input C accounting available budget stage kind risk sample ∂μ := by
      apply setLIntegral_mono' hE
      intro sample hs
      exact tableNextEntryBudget_le_on_entry hlaminar input C hearly accounting available budget hbudget hsmall stage nextStage
        hnextStage history kind risk hk hr sample hs
    change μ (tableStageNoToolFailure input C accounting available budget stage ∩ E) +
      (∫⁻ sample in E, tableEntryBudgetPotential input C accounting available budget nextStage sample ∂μ) ≤
        ENNReal.ofReal ((tableEntryRisk input available budget history).getD 0 : ℝ) * μ E
    rw [hr, Option.getD_some]
    cases kind with
    | infiniteRank =>
      have hzero : μ (tableStageNoToolFailure input C accounting available budget stage ∩ E) = 0 := by
        rw [show tableStageNoToolFailure input C accounting available budget stage ∩ E = ∅ from
          noToolFailure_entry_empty hlaminar input C hearly accounting available budget hbudget hsmall stage history (by rw [hk]; simp)]
        exact measure_empty
      rw [hzero, zero_add]
      simpa only [tableChildBudgetEnvelope, setLIntegral_const] using hi
    | noTool =>
      have he : μ (tableStageWriteError input C accounting available budget stage ∩ E) ≤
          ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E :=
        tableStageWriteError_on_entry_le hlaminar input C hearly accounting available budget hbudget hsmall stage history (risk / 2) ht
      have hf : μ (tableStageNoToolFailure input C accounting available budget stage ∩ E) ≤
          μ (tableStageWriteError input C accounting available budget stage ∩ E) :=
        measure_mono (fun sample hs => (tableNoToolFailure_on_entry_kind hlaminar input C hearly accounting available budget hbudget hsmall stage history hs).2)
      have hchild : (∫⁻ sample in E, tableEntryBudgetPotential input C accounting available budget nextStage sample ∂μ) ≤
          ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E := by
        simpa only [tableChildBudgetEnvelope, setLIntegral_const] using hi
      calc
        _ ≤ μ (tableStageWriteError input C accounting available budget stage ∩ E) +
            ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E := add_le_add hf hchild
        _ = ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E +
            μ (tableStageWriteError input C accounting available budget stage ∩ E) := add_comm _ _
        _ ≤ _ := referenceBudget_noTool_entry_mass risk hv.1.le _ _ he
    | finiteBad depth =>
      have hzero : μ (tableStageNoToolFailure input C accounting available budget stage ∩ E) = 0 := by
        rw [show tableStageNoToolFailure input C accounting available budget stage ∩ E = ∅ from
          noToolFailure_entry_empty hlaminar input C hearly accounting available budget hbudget hsmall stage history (by rw [hk]; simp)]
        exact measure_empty
      rw [hzero, zero_add]
      have he : μ (tableStageWriteError input C accounting available budget stage ∩ E) ≤
          ENNReal.ofReal ((controllerTarget risk depth.val : ℚ) : ℝ) * μ E :=
        tableStageWriteError_on_entry_le hlaminar input C hearly accounting available budget hbudget hsmall stage history _ ht
      have herror := measurableSet_tableStageWriteError input C accounting available budget stage
      have heval : (∫⁻ sample in E, tableChildBudgetEnvelope input C accounting available budget stage (.finiteBad depth) risk sample ∂μ) =
          ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E +
            ENNReal.ofReal ((controllerBadRisk risk (controllerTarget risk depth.val) : ℚ) : ℝ) *
              μ (tableStageWriteError input C accounting available budget stage ∩ E) := by
        simp only [tableChildBudgetEnvelope]
        rw [lintegral_add_right _ (measurable_const.indicator herror), setLIntegral_const,
          lintegral_indicator herror, setLIntegral_const, Measure.restrict_apply herror]
      exact (hi.trans_eq heval).trans (referenceBudget_finiteBad_entry_mass risk hv depth _ _ he)
  · have hEmpty : E = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun sample hs => hex ⟨sample, hs⟩)
    change μ (tableStageNoToolFailure input C accounting available budget stage ∩ E) +
      (∫⁻ sample in E, tableEntryBudgetPotential input C accounting available budget nextStage sample ∂μ) ≤ _
    rw [hEmpty]
    simp

omit hlaminar in
/-- The next-stage budget is zero at the final stage. This is analysis of
the same actual entry selector, not an added terminal operation. -/
noncomputable def tableNextBudgetPotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (sample : Unit × input.World) : ℝ≥0∞ :=
  if h : stage.val + 1 < I.stageCount then
    tableEntryBudgetPotential input C accounting available budget ⟨stage.val + 1, h⟩ sample else 0

omit hlaminar in
theorem measurable_tableNextBudgetPotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    Measurable (tableNextBudgetPotential input C accounting available budget stage) := by
  unfold tableNextBudgetPotential
  split_ifs
  · exact measurable_tableEntryBudgetPotential input C accounting available budget _
  · exact measurable_const

private theorem failureMass_on_entry
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) (history : List (VisibleEvent I)) :
    input.seededWorldLaw (Measure.dirac ())
      (tableStageNoToolFailure input C accounting available budget stage ∩
        tableEntryEvent input C accounting available budget stage history) ≤
      ENNReal.ofReal ((tableEntryRisk input available budget history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (tableEntryEvent input C accounting available budget stage history) := by
  classical
  let μ := input.seededWorldLaw (Measure.dirac ())
  let E := tableEntryEvent input C accounting available budget stage history
  by_cases hex : ∃ sample : Unit × input.World, sample ∈ E
  · obtain ⟨sample, hs⟩ := hex
    obtain ⟨kind, risk, hk, hr, hv, ht⟩ := tableEntryRisk_kind_target hlaminar input C hearly accounting available budget
      hbudget hsmall sample stage history hs
    rw [hr, Option.getD_some]
    cases kind with
    | infiniteRank | finiteBad depth =>
      rw [noToolFailure_entry_empty hlaminar input C hearly accounting available budget hbudget hsmall stage history (by rw [hk]; simp)]
      simp
    | noTool =>
      have he := tableStageWriteError_on_entry_le hlaminar input C hearly accounting available budget hbudget hsmall stage history (risk / 2) ht
      calc
        _ ≤ μ (tableStageWriteError input C accounting available budget stage ∩ E) :=
          measure_mono (fun sample hs => (tableNoToolFailure_on_entry_kind hlaminar input C hearly accounting available budget hbudget hsmall stage history hs).2)
        _ ≤ ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * μ E +
            μ (tableStageWriteError input C accounting available budget stage ∩ E) := le_add_of_nonneg_left zero_le
        _ ≤ _ := referenceBudget_noTool_entry_mass risk hv.1.le _ _ he
  · have hEmpty : E = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun sample hs => hex ⟨sample, hs⟩)
    change μ (_ ∩ E) ≤ _ * μ E
    rw [hEmpty]
    simp

theorem tableBudgetMass_on_entry_allStages
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) (history : List (VisibleEvent I)) :
    input.seededWorldLaw (Measure.dirac ())
        (tableStageNoToolFailure input C accounting available budget stage ∩
          tableEntryEvent input C accounting available budget stage history) +
      (∫⁻ sample in tableEntryEvent input C accounting available budget stage history,
        tableNextBudgetPotential input C accounting available budget stage sample
          ∂input.seededWorldLaw (Measure.dirac ())) ≤
      ENNReal.ofReal ((tableEntryRisk input available budget history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (tableEntryEvent input C accounting available budget stage history) := by
  unfold tableNextBudgetPotential
  split_ifs with hnext
  · exact tableBudgetMass_on_entry hlaminar input C hearly accounting available budget hbudget hsmall
      stage ⟨stage.val + 1, hnext⟩ rfl history
  · simpa only [lintegral_zero, add_zero] using failureMass_on_entry hlaminar input C hearly accounting available budget hbudget hsmall stage history

omit hlaminar in
theorem measurableSet_tableStageNoToolFailure (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    MeasurableSet (tableStageNoToolFailure input C accounting available budget stage) := by
  have heq : tableStageNoToolFailure input C accounting available budget stage =
      ⋃ n : ℕ, (run input C .uncapped accounting (tableRule  input available budget none) · n) ⁻¹'
        {s : State I | ∃ cache : ReferenceReplayCache I,
          s.halted = false ∧ s.cursor = stage.val ∧
            tableRule input available budget none () s.history = .abandon ∧
            tableReplay input available budget s.history = some cache ∧ cache.phase = .reported ∧
            referenceReplayCorrect cache stage = false ∧ tableKind I available cache = some .noTool ∧
            s.ledger.written stage = some (!s.ledger.truth stage)} := by
    ext sample
    have hunit : sample.1 = () := Subsingleton.elim _ _
    simp only [tableStageNoToolFailure, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, hunit]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_run input C .uncapped accounting (tableRule input available budget none)
    (measurable_tableRule input available budget none) n) MeasurableSpace.measurableSet_top

omit hlaminar in
/-- Exact countable entry-atom integration, with no conditioning kernel or
point-mass assumption on the original private seed. -/
theorem lintegral_eq_tsum_tableEntry
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage)
    (f : Unit × input.World → ℝ≥0∞) (hf : Measurable f)
    (hzero : ∀ sample, entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = none → f sample = 0) :
    (∫⁻ sample, f sample ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I), ∫⁻ sample in tableEntryEvent input C accounting available budget stage history,
        f sample ∂input.seededWorldLaw (Measure.dirac ()) := by
  classical
  have hsplit : ∀ sample, f sample = ∑' history : List (VisibleEvent I),
      (tableEntryEvent input C accounting available budget stage history).indicator f sample := by
    intro sample
    cases he : entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample with
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
        _ = (tableEntryEvent input C accounting available budget stage history).indicator f sample := by
          apply tsum_eq_single history
          intro other hne
          apply Set.indicator_of_notMem
          intro hh
          exact hne (Option.some.inj (hh.symm.trans he))
        _ = f sample := Set.indicator_of_mem (show sample ∈ tableEntryEvent input C accounting available budget stage history from he) f
  calc
    _ = ∫⁻ sample, ∑' history : List (VisibleEvent I),
        (tableEntryEvent input C accounting available budget stage history).indicator f sample
          ∂input.seededWorldLaw (Measure.dirac ()) := lintegral_congr hsplit
    _ = ∑' history : List (VisibleEvent I), ∫⁻ sample,
        (tableEntryEvent input C accounting available budget stage history).indicator f sample
          ∂input.seededWorldLaw (Measure.dirac ()) :=
      lintegral_tsum (fun history => (hf.indicator (measurableSet_tableEntryEvent input C accounting available budget stage history)).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro history
      exact lintegral_indicator (measurableSet_tableEntryEvent input C accounting available budget stage history) f

theorem tableNextBudget_zero_of_no_entry
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) (sample : Unit × input.World)
    (hnone : entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = none) :
    tableNextBudgetPotential input C accounting available budget stage sample = 0 := by
  unfold tableNextBudgetPotential
  split_ifs with hnext
  · cases he : entryHistory input C .uncapped accounting (tableRule input available budget none) ⟨stage.val + 1, hnext⟩ sample with
    | none => simp [tableEntryBudgetPotential, he]
    | some nextHistory =>
      obtain ⟨n, s, next, hp, _, hs, ha, _⟩ := tableNextEntry_has_advance input C hearly accounting available budget
        sample stage ⟨stage.val + 1, hnext⟩ rfl nextHistory he
      obtain ⟨cache, history, kind, risk, _, hentry, _⟩ := tableAdvance_entry_budget hlaminar input C hearly accounting available budget
        hbudget hsmall sample hp stage ⟨stage.val + 1, hnext⟩ rfl hs ha
      rw [hnone] at hentry
      cases hentry
  · rfl

private theorem failureMass_eq_tsum_entry
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ()) (tableStageNoToolFailure input C accounting available budget stage) =
      ∑' history : List (VisibleEvent I), input.seededWorldLaw (Measure.dirac ())
        (tableStageNoToolFailure input C accounting available budget stage ∩
          tableEntryEvent input C accounting available budget stage history) := by
  classical
  let F := tableStageNoToolFailure input C accounting available budget stage
  have hF : MeasurableSet F := measurableSet_tableStageNoToolFailure input C accounting available budget stage
  have hzero : ∀ sample : Unit × input.World,
      entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = none →
        F.indicator (fun _ => (1 : ℝ≥0∞)) sample = 0 := by
    intro sample hnone
    apply Set.indicator_of_notMem
    intro hs
    obtain ⟨history, hentry, _⟩ := tableNoToolFailure_entry_kind hlaminar input C hearly accounting available budget hbudget hsmall stage sample hs
    rw [hnone] at hentry
    cases hentry
  have hx := lintegral_eq_tsum_tableEntry input C accounting available budget stage
    (F.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hF) hzero
  simpa only [lintegral_indicator_const hF, one_mul, Measure.restrict_apply hF] using hx

omit hlaminar in
private theorem currentBudgetMass_eq_tsum_entry
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    (∫⁻ sample, tableEntryBudgetPotential input C accounting available budget stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I), ENNReal.ofReal ((tableEntryRisk input available budget history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (tableEntryEvent input C accounting available budget stage history) := by
  rw [lintegral_eq_tsum_tableEntry input C accounting available budget stage _
    (measurable_tableEntryBudgetPotential input C accounting available budget stage)
    (fun sample hs => by simp only [tableEntryBudgetPotential, hs])]
  apply tsum_congr
  intro history
  calc
    _ = ∫⁻ _sample in tableEntryEvent input C accounting available budget stage history,
        ENNReal.ofReal ((tableEntryRisk input available budget history).getD 0 : ℝ)
          ∂input.seededWorldLaw (Measure.dirac ()) := by
      apply setLIntegral_congr_fun (measurableSet_tableEntryEvent input C accounting available budget stage history)
      intro sample hs
      simp only [tableEntryBudgetPotential, show entryHistory input C .uncapped accounting
        (tableRule input available budget none) stage sample = some history from hs]
    _ = _ := setLIntegral_const _ _

/-- The true probability-weighted stage recursion. All current-entry atoms
are summed using the real record law; unentered histories contribute zero.
No eventual-success restriction, finite-cost premise or risk assumption occurs. -/
theorem tableStage_budget_mass_nonincreasing
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ()) (tableStageNoToolFailure input C accounting available budget stage) +
      (∫⁻ sample, tableNextBudgetPotential input C accounting available budget stage sample
        ∂input.seededWorldLaw (Measure.dirac ())) ≤
      ∫⁻ sample, tableEntryBudgetPotential input C accounting available budget stage sample
        ∂input.seededWorldLaw (Measure.dirac ()) := by
  have hnext := lintegral_eq_tsum_tableEntry input C accounting available budget stage _
    (measurable_tableNextBudgetPotential input C accounting available budget stage)
    (tableNextBudget_zero_of_no_entry hlaminar input C hearly accounting available budget hbudget hsmall stage)
  calc
    _ = (∑' history : List (VisibleEvent I), input.seededWorldLaw (Measure.dirac ())
          (tableStageNoToolFailure input C accounting available budget stage ∩
            tableEntryEvent input C accounting available budget stage history)) +
        (∑' history : List (VisibleEvent I), ∫⁻ sample in tableEntryEvent input C accounting available budget stage history,
          tableNextBudgetPotential input C accounting available budget stage sample ∂input.seededWorldLaw (Measure.dirac ())) := by
      rw [failureMass_eq_tsum_entry hlaminar input C hearly accounting available budget hbudget hsmall stage, hnext]
    _ = ∑' history : List (VisibleEvent I),
        (input.seededWorldLaw (Measure.dirac ()) (tableStageNoToolFailure input C accounting available budget stage ∩
          tableEntryEvent input C accounting available budget stage history) +
          ∫⁻ sample in tableEntryEvent input C accounting available budget stage history,
            tableNextBudgetPotential input C accounting available budget stage sample ∂input.seededWorldLaw (Measure.dirac ())) := ENNReal.tsum_add.symm
    _ ≤ ∑' history : List (VisibleEvent I), ENNReal.ofReal ((tableEntryRisk input available budget history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (tableEntryEvent input C accounting available budget stage history) :=
      ENNReal.tsum_le_tsum (tableBudgetMass_on_entry_allStages hlaminar input C hearly accounting available budget hbudget hsmall stage)
    _ = _ := (currentBudgetMass_eq_tsum_entry input C accounting available budget stage).symm

omit hlaminar in
/-- Budget mass before cursor k, with the terminal mass fixed to zero. -/
noncomputable def tableBudgetMassAt (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (k : ℕ) : ℝ≥0∞ :=
  if h : k < I.stageCount then
    ∫⁻ sample, tableEntryBudgetPotential input C accounting available budget ⟨k, h⟩ sample
      ∂input.seededWorldLaw (Measure.dirac ()) else 0

omit hlaminar in
noncomputable def tableFailureMassAt (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (k : ℕ) : ℝ≥0∞ :=
  if h : k < I.stageCount then
    input.seededWorldLaw (Measure.dirac ()) (tableStageNoToolFailure input C accounting available budget ⟨k, h⟩) else 0

theorem tableBudgetMassAt_step
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (k : ℕ) (hk : k < I.stageCount) :
    tableFailureMassAt input C accounting available budget k + tableBudgetMassAt input C accounting available budget (k + 1) ≤
      tableBudgetMassAt input C accounting available budget k := by
  have hn : tableBudgetMassAt input C accounting available budget (k + 1) =
      ∫⁻ sample, tableNextBudgetPotential input C accounting available budget ⟨k, hk⟩ sample
        ∂input.seededWorldLaw (Measure.dirac ()) := by
    by_cases hnext : k + 1 < I.stageCount <;>
      simp only [tableBudgetMassAt, tableNextBudgetPotential, hnext, ↓reduceDIte, lintegral_zero]
  rw [hn]
  simp only [tableFailureMassAt, tableBudgetMassAt, hk, dite_true]
  exact tableStage_budget_mass_nonincreasing hlaminar input C hearly accounting available budget hbudget hsmall ⟨k, hk⟩

omit hlaminar in
theorem tableBudgetMassAt_terminal (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) :
    tableBudgetMassAt input C accounting available budget I.stageCount = 0 := by
  simp only [tableBudgetMassAt, lt_self_iff_false, dite_false]

omit hlaminar in
/-- The actual stage-zero record is [], so the initial budget mass is at
most the original budget/2 (zero for an empty task). -/
theorem tableBudgetMassAt_initial
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    tableBudgetMassAt input C accounting available budget 0 ≤ ENNReal.ofReal ((budget / 2 : ℚ) : ℝ) := by
  by_cases hzero : 0 < I.stageCount
  · simp only [tableBudgetMassAt, hzero, dite_true]
    have hpoint : ∀ sample : Unit × input.World,
        tableEntryBudgetPotential input C accounting available budget ⟨0, hzero⟩ sample =
          ENNReal.ofReal ((budget / 2 : ℚ) : ℝ) := by
      intro sample
      have he := entryHistory_stageZero input C .uncapped accounting (tableRule  input available budget none)
        ⟨0, hzero⟩ rfl sample
      simp only [tableEntryBudgetPotential, he, tableEntryRisk_initial input available budget hbudget hsmall, Option.getD_some]
    calc
      _ = ∫⁻ _sample : Unit × input.World, ENNReal.ofReal ((budget / 2 : ℚ) : ℝ)
          ∂input.seededWorldLaw (Measure.dirac ()) := lintegral_congr hpoint
      _ ≤ ENNReal.ofReal ((budget / 2 : ℚ) : ℝ) := by simp
  · simp only [tableBudgetMassAt, hzero, dite_false]
    exact zero_le

/-- The complete original ideal-reference risk bound. The actual failure
events are bounded by a finite positive-term budget telescope, after the
real entry-law mass recursion. Failed paths and unentered histories remain
in the original run measure; no risk/termination/alignment premise is added. -/
theorem tableIdealRisk_le_half
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    risk input C .uncapped accounting (tableRule input available budget none) (Measure.dirac ()) ≤
      ENNReal.ofReal ((budget : ℝ) / 2) := by
  have hsum : (∑ stage : I.Stage, input.seededWorldLaw (Measure.dirac ())
      (tableStageNoToolFailure input C accounting available budget stage)) =
      ∑ k ∈ Finset.range I.stageCount, tableFailureMassAt input C accounting available budget k := by
    calc
      _ = ∑ stage : I.Stage, tableFailureMassAt input C accounting available budget stage.val := by
        apply Finset.sum_congr rfl
        intro stage _
        unfold tableFailureMassAt
        rw [dite_eq_left (show stage.val < I.stageCount from stage.isLt)]
      _ = _ := Fin.sum_univ_eq_sum_range _ I.stageCount
  calc
    _ ≤ ∑ stage : I.Stage, input.seededWorldLaw (Measure.dirac ())
        (tableStageNoToolFailure input C accounting available budget stage) :=
      tableRisk_le_sum_noToolFailure hlaminar input C hearly accounting available budget hbudget hsmall
    _ = ∑ k ∈ Finset.range I.stageCount, tableFailureMassAt input C accounting available budget k := hsum
    _ ≤ ENNReal.ofReal ((budget / 2 : ℚ) : ℝ) :=
      referenceFailureMass_sum_le_initial (tableFailureMassAt input C accounting available budget)
        (tableBudgetMassAt input C accounting available budget) I.stageCount _
        (tableBudgetMassAt_step hlaminar input C hearly accounting available budget hbudget hsmall)
        (tableBudgetMassAt_initial input C accounting available budget hbudget hsmall)
    _ = _ := by
      congr 1
      push_cast
      rfl


end PaperProofs.Common.Native.PSTRStatistics.TableMass
