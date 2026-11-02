module

public import PaperProofs.Common.PSTR_ST_TableInfinite_009
public import PaperProofs.Common.ReferenceTermination

/-! Actual table ideal termination, success-at-stop and real no-tool failure
classification. Null local infinite-review paths give a.s. halting; neither
termination nor final risk is supplied as a policy or cache hypothesis. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.TableTermination

open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree CompactPrice TableAlignment TableOrigin TableDecision TableInfinite

variable {I : Instance} (hlaminar : LaminarSchedule I.compatibility)
include hlaminar

omit hlaminar in
private theorem some_if_some {α : Type*} (P : Prop) [Decidable P] (value next : α)
    (h : (if P then some value else none) = some next) : P ∧ next = value := by
  by_cases hp : P
  · rw [ite_eq_left hp] at h
    exact ⟨hp, (Option.some.inj h).symm⟩
  · rw [ite_eq_right hp] at h
    cases h

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
/-- If all actual local review-request counts are bounded on one sample,
the ideal reference halts on that sample. No deterministic uniform review
bound or future-success restriction is supplied. -/
theorem tableRun_halts_of_not_infinite_reviews
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (sample : Unit × input.World)
    (hfinite : ∀ stage : I.Stage,
      sample ∉ tableStageInfiniteReviews input C hearly accounting available budget stage) :
    ∃ n, (run input C .uncapped accounting (tableRule input available budget none) sample n).halted = true := by
  classical
  have hthreshold : ∀ stage : I.Stage, ∃ threshold : ℕ,
      sample ∉ tableStageOverflow input C hearly accounting available budget (fun _ => threshold) stage := by
    intro stage
    by_contra h
    apply hfinite stage
    intro threshold
    exact not_not.mp (not_exists.mp h threshold)
  choose quota hquota using hthreshold
  have hgate : ∀ (n : ℕ) (s : State I),
      Prefix input C .uncapped accounting (tableRule input available budget none) sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) n s → s.halted = false →
      ∀ stage : I.Stage, tableRule input available budget none sample.1 s.history = .review stage →
        s.ledger.reviews stage < (quota stage : ℕ∞) := by
    intro n s hp hactive stage haction
    by_contra hnot
    have hcount : (quota stage : ℕ∞) ≤ s.ledger.reviews stage := le_of_not_gt hnot
    apply hquota stage
    have hrun := prefix_eq_run_sample input C accounting (tableRule input available budget none) sample hp
    have hunit : sample.1 = () := Subsingleton.elim _ _
    refine ⟨n, ?_⟩
    simpa only [tableIdealPolicy, tableUncappedPolicy, hrun] using
      (show s.halted = false ∧ tableRule input available budget none () s.history = .review stage ∧
        ((fun _ : I.Stage => quota stage) stage : ℕ∞) ≤ s.ledger.reviews stage from
        ⟨hactive, by simpa only [hunit] using haction, hcount⟩)
  by_contra hnever
  let bound := reviewBoundedActionBound I quota
  have hactive : (run input C .uncapped accounting (tableRule input available budget none) sample (bound + 1)).halted = false :=
    Bool.eq_false_iff.mpr (not_exists.mp hnever (bound + 1))
  have hp := run_prefix_of_active input C .uncapped accounting (tableRule input available budget none)
    (tableRule_uncapped_legal input C hearly accounting available budget none) sample (bound + 1) hactive
  have hb := prefix_reviews_le_of_review_gate input C .uncapped accounting (tableRule input available budget none)
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) quota hgate hp
  have hn := prefix_length_le_of_reviews_bounded input C .uncapped accounting (tableRule input available budget none)
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp quota hb
  omega

omit hlaminar in
/-- Every nonhalting ideal reference sample has some genuinely unbounded
local review stream. This is a real-path statement with no measure premise. -/
theorem tableRun_nonhalting_has_infinite_reviews
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (sample : Unit × input.World)
    (hnever : ¬ ∃ n, (run input C .uncapped accounting (tableRule input available budget none) sample n).halted = true) :
    ∃ stage : I.Stage, sample ∈ tableStageInfiniteReviews input C hearly accounting available budget stage := by
  classical
  by_contra h
  apply hnever
  apply tableRun_halts_of_not_infinite_reviews input C hearly accounting available budget sample
  exact not_exists.mp h

/-- Actual uncapped ideal-reference termination is almost sure for every
initial availability and original valid rational risk. Local finite ET and
the real execution identification are the only probability inputs. -/
theorem tableRun_ae_halts
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    ∀ᵐ sample ∂input.seededWorldLaw (Measure.dirac ()),
      ∃ n, (run input C .uncapped accounting (tableRule input available budget none) sample n).halted = true := by
  have hlocal : ∀ stage : I.Stage,
      ∀ᵐ sample ∂input.seededWorldLaw (Measure.dirac ()),
        sample ∉ tableStageInfiniteReviews input C hearly accounting available budget stage := by
    intro stage
    apply ae_iff.mpr
    have heq : {sample : Unit × input.World |
        ¬ sample ∉ tableStageInfiniteReviews input C hearly accounting available budget stage} =
        tableStageInfiniteReviews input C hearly accounting available budget stage := by
      ext sample
      simp
    rw [heq]
    exact tableStageInfiniteReviews_measure_zero input hlaminar C hearly accounting available budget hbudget hsmall stage
  filter_upwards [ae_all_iff.mpr hlocal] with sample hsample
  exact tableRun_halts_of_not_infinite_reviews input C hearly accounting available budget sample hsample

theorem tableRun_nontermination_measure_zero
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    input.seededWorldLaw (Measure.dirac ()) {sample : Unit × input.World |
      ¬ ∃ n, (run input C .uncapped accounting (tableRule input available budget none) sample n).halted = true} = 0 :=
  ae_iff.mp (tableRun_ae_halts hlaminar input C hearly accounting available budget hbudget hsmall)

omit hlaminar in
private theorem cursor_of_stage (cache : ReferenceReplayCache I) (stage : I.Stage)
    (hstage : referenceReplayStage I cache = some stage) : historyCursor cache.seen = stage.val := by
  unfold referenceReplayStage at hstage
  split_ifs at hstage with hb
  exact congrArg (fun i : I.Stage => i.val) (Option.some.inj hstage)

private theorem rankCase_noTool_of_repair_none (available : Finset I.Tool) (stage : I.Stage)
    (used : Finset I.Tool) (kind : ReferenceBudgetCase)
    (hcase : referenceAvailableRankCase I available stage used = some kind)
    (hpick : tableRepairTool I available stage used = none) : kind = .noTool := by
  have hbad := (badChildRank_eq_zero_iff (I.eligible stage) (I.compatibility.drop (stage.val + 1))
    (available \ used)).mpr ((tableRepairTool_eq_none I hlaminar available stage used).mp hpick)
  have hs := referenceAvailableRankCase_semantics I available stage used kind hcase
  cases kind with
  | noTool => rfl
  | infiniteRank =>
    rw [List.drop_eq_getElem_cons stage.isLt] at hs
    have ht := ((errorRank_cons_eq_top_iff _ _ _).mp hs).2
    exact (ENat.zero_ne_top (hbad.symm.trans ht)).elim
  | finiteBad depth =>
    have hz : (depth.val : ℕ∞) = 0 := hs.2.symm.trans hbad
    have hn : depth.val = 0 := by exact_mod_cast hz
    exact (Nat.ne_of_gt depth.pos hn).elim

/-- The ideal testing phase cannot abort at a genuine aligned prefix.
This uses the real valid word and positive entry budget, not a successful
future path, and includes zero-sample threshold hits. -/
theorem tableTestingAction_ideal_ne_abandon 
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Unit) (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting rule seed truth tapes n s)
    (available : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I)
    (haligned : TableStateAligned input available budget cache s)
    (hphase : cache.phase = .testing) (hactive : s.halted = false)
    (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    tableTestingAction input available budget none cache stage ≠ .abandon := by
  obtain ⟨kind, current, hkind, hcurrent, hv, hlen⟩ :=
    tableStateAligned_testing_ready hlaminar input available budget cache s haligned hphase stage hcursor
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hword : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize := by
    rw [haligned.seen]
    exact prefix_historyObservation_alphabet input C .uncapped accounting rule seed truth tapes hp stage
  cases kind with
  | infiniteRank => simp [tableTestingAction, hkind]
  | noTool =>
    have ht : tableTarget I available budget cache = some (current / 2) := by
      simp [tableTarget, hh, hphase, hkind, hcurrent,
        hv.1, Nat.le_of_lt hlen, referenceBudgetTarget]
      simpa only [one_div] using hv.2
    simp only [tableTestingAction, hkind, ht, dite_eq_left hword]
    split_ifs <;> simp
  | finiteBad depth =>
    have ht : tableTarget I available budget cache = some (controllerTarget current depth.val) := by
      simp [tableTarget, hh, hphase, hkind, hcurrent,
        hv.1, Nat.le_of_lt hlen, referenceBudgetTarget]
      simpa only [one_div] using hv.2
    simp only [tableTestingAction, hkind, ht, dite_eq_left hword]
    split_ifs <;> simp

/-- Actual ideal abandonment can occur only immediately after a reported
no-tool error. Parser/ledger alignment is derived from the actual Prefix,
and the wrong ordinary bit is read from the actual ledger. -/
theorem tableRule_abandon_noTool_error 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget none) seed truth tapes n s)
    (hactive : s.halted = false)
    (haction : tableRule input available budget none seed s.history = .abandon) :
    ∃ (stage : I.Stage) (cache : ReferenceReplayCache I),
      TableStateAligned input available budget cache s ∧ s.cursor = stage.val ∧
      cache.phase = .reported ∧ referenceReplayCorrect cache stage = false ∧
      tableKind I available cache = some .noTool ∧
      s.ledger.written stage = some (!s.ledger.truth stage) := by
  obtain ⟨cache, haligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget
    hbudget hsmall none seed truth tapes hp
  have hh : cache.halted = false := haligned.halted.trans hactive
  have ha : tableCandidate input available budget none s.history = .abandon :=
    (tableRule_eq_candidate_of_prefix hlaminar input C hearly accounting available budget hbudget hsmall none
      seed truth tapes hp).symm.trans haction
  cases hstage : referenceReplayStage I cache with
  | none =>
    have hb := (prefix_cursorInvariant input C .uncapped accounting
      (tableRule input available budget none) seed truth tapes hp).bound
    have hnot : ¬ historyCursor cache.seen < I.stageCount := by
      intro h
      simp [referenceReplayStage, h] at hstage
    have hcursor : historyCursor s.history = I.stageCount := by
      rw [← haligned.seen, haligned.cursor]
      rw [haligned.cursor] at hnot
      omega
    simp [tableCandidate, haligned.parsed, hh, hstage, hcursor] at ha
  | some stage =>
    have hc : s.cursor = stage.val := haligned.cursor.symm.trans (cursor_of_stage cache stage hstage)
    cases hphase : cache.phase with
    | testing =>
      have ht : tableTestingAction input available budget none cache stage = .abandon := by
        simpa only [tableCandidate, haligned.parsed, hh, Bool.false_eq_true, ite_false, hstage, hphase] using ha
      exact (tableTestingAction_ideal_ne_abandon hlaminar input C accounting (tableRule input available budget none)
        seed truth tapes hp available budget cache haligned hphase hactive stage hc ht).elim
    | written => exact ((tableReplay_some_spec input available budget s.history cache haligned.parsed).2.2.1 hphase).elim
    | reported =>
      have hf := haligned.current_fields stage hc
      simp only [referenceCurrentLedgerFits, hphase] at hf
      obtain ⟨bit, hwritten⟩ := Option.ne_none_iff_exists'.mp hf.1
      have hw := prefix_historyWrite input C .uncapped accounting (tableRule input available budget none)
        seed truth tapes hp stage
      rw [hwritten] at hw
      let handle : MismatchHandle I := ⟨stage, s.ledger.writeSerial stage⟩
      have hvisible : referenceVisibleHandle s.history stage = some handle := by
        simp [referenceVisibleHandle, hw, handle]
      cases hcorrect : referenceReplayCorrect cache stage with
      | true => simp [tableCandidate, haligned.parsed, hh, hstage, hphase, hcorrect] at ha
      | false =>
        obtain ⟨kind, entryRisk, hkind, _, hupdate⟩ := haligned.reported_update
          (by simp [hphase, referencePhaseReportCount]) stage hc
        have hcase : referenceAvailableRankCase I available stage (historyUsed cache.entryHistory) = some kind := by
          have hgeneric : referenceAvailableKind I available cache = some kind :=
            (callbackFormulaClaims I hlaminar available cache budget).1.symm.trans hkind
          simpa only [referenceAvailableKind, hstage, Option.bind_eq_bind, Option.bind_some] using hgeneric
        have hkindNoTool : kind = .noTool := by
          cases hrisk : referenceReplayRisk budget cache with
          | none =>
            rw [hrisk, hcorrect] at hupdate
            cases kind <;> simp [referenceBudgetStep] at hupdate ⊢
          | some current =>
            cases hpick : tableRepairTool I available stage (historyUsed cache.entryHistory) with
            | none => exact rankCase_noTool_of_repair_none hlaminar available stage (historyUsed cache.entryHistory) kind hcase hpick
            | some tool =>
              simp [tableCandidate, haligned.parsed, hh, hstage, hphase, hcorrect, hrisk, hvisible, hpick] at ha
        have hvalid := (tableStateAligned_reported_mismatch input C hearly accounting
          (tableRule input available budget none) seed truth tapes hp available budget cache haligned
          hphase stage hc hcorrect handle hvisible).1
        refine ⟨stage, cache, haligned, hc, hphase, hcorrect, ?_, ?_⟩
        · simpa only [hkindNoTool] using hkind
        · exact hvalid.1
    | allocated tool =>
      obtain ⟨handle, hs, hvalid, _, _, _, _⟩ := by
        simpa only [referenceCurrentLedgerFits, hphase] using haligned.current_fields stage hc
      have hvisible := prefix_visibleHandle_of_valid input C hearly .uncapped accounting
        (tableRule input available budget none) seed truth tapes hp handle hvalid
      rw [hs] at hvisible
      simp [tableCandidate, haligned.parsed, hh, hstage, hphase, hvisible] at ha
    | executed tool => simp [tableCandidate, haligned.parsed, hh, hstage, hphase] at ha

/-- A real ideal-reference stop is successful for every initial available
set, including finite rank. Abandonment is a different, explicit action. -/
theorem tableRule_stop_success 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget none) seed truth tapes n s)
    (hactive : s.halted = false)
    (haction : tableRule input available budget none seed s.history = .stop) :
    (stopState s false).ledger.success C := by
  classical
  have hpnext : Prefix input C .uncapped accounting (tableRule input available budget none)
      seed truth tapes (n + 1) (stopState s false) := .next hp (haction ▸ .stop s hactive)
  obtain ⟨cache, haligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget
    hbudget hsmall none seed truth tapes hp
  obtain ⟨nextCache, hnextAligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget
    hbudget hsmall none seed truth tapes hpnext
  have hs := tableReplay_some_spec input available budget s.history cache haligned.parsed
  have hs' := tableReplay_some_spec input available budget (s.history ++ [.stopped]) nextCache hnextAligned.parsed
  rw [List.foldlM_append, hs.2.1] at hs'
  have hsingle : tableStep input available budget cache .stopped = some nextCache := by
    simpa using hs'.2.1
  have hh : cache.halted = false := haligned.halted.trans hactive
  simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hsingle
  obtain ⟨hg, _⟩ := some_if_some _ _ _ hsingle
  have hcursor : s.cursor = I.stageCount := haligned.cursor.symm.trans hg.1
  have hcorrect (stage : I.Stage) : s.ledger.written stage = some (s.ledger.truth stage) ∨
      ∃ e ∈ s.ledger.executions, e.handle.stage = stage :=
    prefix_table_pastCorrect hlaminar input C hearly accounting available budget hbudget hsmall none
      seed truth tapes hp stage (hcursor ▸ stage.isLt)
  have hwf := prefix_ledgerWellFormed input C .uncapped accounting
    (tableRule input available budget none) seed truth tapes hp
  have hall : allWritten s.ledger := by
    intro stage
    rcases hcorrect stage with hw | ⟨e, he, hs⟩
    · rw [hw]; simp
    · have hg := (hwf.genuine e he).1
      rw [hs] at hg
      rw [hg]; simp
  apply (prefix_success_iff_physical input C .uncapped accounting
    (tableRule input available budget none) seed truth tapes hpnext).mpr
  refine ⟨?_, rfl, ?_⟩
  · change decide (allWritten s.ledger) = true
    exact decide_eq_true hall
  · intro stage
    exact (finalOutput_correct_iff _ stage).mpr (hcorrect stage)

omit hlaminar in
/-- A finite-stage failure source in the real ideal run. The report and
ordinary error are actual ledger data, and rank uses the original entry
availability snapshot. No successful-future conditioning is present. -/
def tableStageNoToolFailure (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    Set (Unit × input.World) :=
  {sample | ∃ (n : ℕ) (cache : ReferenceReplayCache I),
    let s := run input C .uncapped accounting (tableRule input available budget none) sample n
    s.halted = false ∧ s.cursor = stage.val ∧
      tableRule input available budget none sample.1 s.history = .abandon ∧
      tableReplay input available budget s.history = some cache ∧
      cache.phase = .reported ∧ referenceReplayCorrect cache stage = false ∧
      tableKind I available cache = some .noTool ∧
      s.ledger.written stage = some (!s.ledger.truth stage)}

private theorem prefix_halted_success_or_noToolFailure
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget none)
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n s) (hhalt : s.halted = true) :
    s.ledger.success C ∨ ∃ stage : I.Stage,
      sample ∈ tableStageNoToolFailure input C accounting available budget stage := by
  cases hp with
  | initial => cases hhalt
  | @next n s next earlier step =>
    generalize haction : tableRule input available budget none sample.1 s.history = action at step
    cases step with
    | review current live port resources => cases hhalt
    | write current bit live port resources => cases hhalt
    | allocate handle tool active valid compatible unused unallocated window resources => cases hhalt
    | execute handle tool active valid compatible committed unused uncorrected window resources => cases hhalt
    | advance stage live written resources => cases hhalt
    | stop active =>
      exact Or.inl (tableRule_stop_success hlaminar input C hearly accounting available budget hbudget hsmall
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier active haction)
    | abandon active =>
      obtain ⟨stage, cache, haligned, hcursor, hphase, hcorrect, hkind, hwrong⟩ :=
        tableRule_abandon_noTool_error hlaminar input C hearly accounting available budget hbudget hsmall
          sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier active haction
      refine Or.inr ⟨stage, n, cache, ?_⟩
      rw [prefix_eq_run_sample input C accounting (tableRule input available budget none) sample earlier]
      exact ⟨active, hcursor, haction, haligned.parsed, hphase, hcorrect, hkind, hwrong⟩

/-- Every actual failed ideal run either does not halt or has a finite
reported no-tool error. The first alternative is already a proved null set. -/
theorem tableFailure_subset_nontermination_union_noTool
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    {sample : Unit × input.World |
      ¬ runSuccess input C .uncapped accounting (tableRule input available budget none) sample} ⊆
    {sample : Unit × input.World | ¬ ∃ n,
      (run input C .uncapped accounting (tableRule input available budget none) sample n).halted = true} ∪
      ⋃ stage : I.Stage, tableStageNoToolFailure input C accounting available budget stage := by
  intro sample hfailure
  by_cases hhalt : ∃ n, (run input C .uncapped accounting (tableRule input available budget none) sample n).halted = true
  · obtain ⟨n, hh⟩ := hhalt
    obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (tableRule input available budget none)
      (tableRule_uncapped_legal input C hearly accounting available budget none) sample n
    rcases prefix_halted_success_or_noToolFailure hlaminar input C hearly accounting available budget hbudget hsmall sample hp hh with
      hsuccess | ⟨stage, hstage⟩
    · exact (hfailure ⟨n, hh, hsuccess⟩).elim
    · exact Or.inr (Set.mem_iUnion.mpr ⟨stage, hstage⟩)
  · exact Or.inl hhalt

theorem tableRisk_le_sum_noToolFailure
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    risk input C .uncapped accounting (tableRule input available budget none) (Measure.dirac ()) ≤
      ∑ stage : I.Stage, input.seededWorldLaw (Measure.dirac ())
        (tableStageNoToolFailure input C accounting available budget stage) := by
  calc
    _ ≤ input.seededWorldLaw (Measure.dirac ())
        ({sample : Unit × input.World | ¬ ∃ n,
          (run input C .uncapped accounting (tableRule input available budget none) sample n).halted = true} ∪
            ⋃ stage : I.Stage, tableStageNoToolFailure input C accounting available budget stage) :=
      measure_mono (tableFailure_subset_nontermination_union_noTool hlaminar input C hearly accounting available budget hbudget hsmall)
    _ ≤ input.seededWorldLaw (Measure.dirac ()) {sample : Unit × input.World | ¬ ∃ n,
          (run input C .uncapped accounting (tableRule input available budget none) sample n).halted = true} +
        input.seededWorldLaw (Measure.dirac ()) (⋃ stage : I.Stage, tableStageNoToolFailure input C accounting available budget stage) :=
      measure_union_le _ _
    _ ≤ 0 + ∑ stage : I.Stage, input.seededWorldLaw (Measure.dirac ())
        (tableStageNoToolFailure input C accounting available budget stage) := by
      rw [tableRun_nontermination_measure_zero hlaminar input C hearly accounting available budget hbudget hsmall]
      simpa only [zero_add, tsum_fintype] using
        (measure_iUnion_le (μ := input.seededWorldLaw (Measure.dirac ()))
          (fun stage : I.Stage => tableStageNoToolFailure input C accounting available budget stage))
    _ = _ := zero_add _


end PaperProofs.Common.Native.PSTRStatistics.TableTermination
