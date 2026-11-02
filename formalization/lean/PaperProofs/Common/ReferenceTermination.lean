module

public import PaperProofs.Common.ReferenceCompletion

/-!
Almost-sure returned-action termination of the original ideal reference.
Finite review-request thresholds are obtained separately on each sample from
the already-proved null local infinite-review events. The structural action
count below uses no Native quota, H0, success, or termination Policy field.
Actual stopping is successful; actual abandonment is identified as a reported
no-tool ordinary error. Risk is bounded by the finite sum of these genuine
failure-source masses. The remaining entry-budget telescoping bound is not
postulated or proved by this module, so general ReferenceRiskGuarantee remains open.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

private theorem reportedWrite_reviews (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

private theorem some_if_some {α : Type*} (P : Prop) [Decidable P] (value next : α)
    (h : (if P then some value else none) = some next) : P ∧ next = value := by
  by_cases hp : P
  · rw [ite_eq_left hp] at h
    exact ⟨hp, (Option.some.inj h).symm⟩
  · rw [ite_eq_right hp] at h
    cases h

/-- A bound on actual requests implies the corresponding bound on paid
reviews, including every failed prefix. The premise is a request-level
statement, not a property assumed in the controller's Policy. -/
theorem prefix_reviews_le_of_review_gate {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (quota : I.Stage → ℕ)
    (hgate : ∀ (n : ℕ) (s : State I), Prefix input C mode accounting rule seed truth tapes n s →
      s.halted = false → ∀ stage : I.Stage, rule seed s.history = .review stage →
        s.ledger.reviews stage < (quota stage : ℕ∞))
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    ∀ stage : I.Stage, s.ledger.reviews stage ≤ (quota stage : ℕ∞) := by
  induction hp with
  | initial => intro stage; exact bot_le
  | @next n s next earlier step ih =>
    generalize haction : rule seed s.history = action at step
    cases step with
    | review current live port resources =>
      have hstrict := hgate n s earlier live.1 current haction
      intro stage
      by_cases heq : stage = current
      · subst stage
        have hfinite := prefix_reviews_natCast_toNat input C mode accounting rule seed truth tapes earlier current
        have hnat : (s.ledger.reviews current).toNat < quota current := by
          exact ENat.natCast_lt_natCast.mp (by simpa only [hfinite] using hstrict)
        simp only [record, reviewLedger, Function.update_self]
        rw [← hfinite, ← ENat.natCast_one, ← ENat.natCast_add]
        exact ENat.natCast_le_natCast.mpr (Nat.succ_le_of_lt hnat)
      · simpa only [record, reviewLedger, Function.update_of_ne heq] using ih stage
    | write current bit live port resources =>
      intro stage
      simpa only [record, reportedWrite_reviews] using ih stage
    | allocate | execute | advance | stop | abandon => exact ih

/-- The finite bound here is a sample-specific analysis threshold, never an
interface quota and never a modification of the actual ideal rule. -/
def reviewBoundedActionBound (I : Instance) (quota : I.Stage → ℕ) : ℕ :=
  (∑ stage, quota stage) + I.toolCount + I.toolCount + I.stageCount + I.stageCount + 1

private theorem enat_natCast_sum {α : Type*} (items : Finset α) (f : α → ℕ) :
    ((∑ item ∈ items, f item : ℕ) : ℕ∞) = ∑ item ∈ items, (f item : ℕ∞) := by
  classical
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item items hnot ih => simp only [Finset.sum_insert hnot, ENat.natCast_add, ih]

/-- This bound is valid in every resource mode and follows from actual
counts. It does not transfer a Native horizon onto an uncapped policy. -/
theorem prefix_length_le_of_reviews_bounded {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (quota : I.Stage → ℕ) (hbound : ∀ stage : I.Stage, s.ledger.reviews stage ≤ (quota stage : ℕ∞)) :
    n ≤ reviewBoundedActionBound I quota := by
  have hwf := prefix_ledgerWellFormed input C mode accounting rule seed truth tapes hp
  have hcursor := (prefix_cursorInvariant input C mode accounting rule seed truth tapes hp).bound
  have hreviews : (∑ stage, s.ledger.reviews stage) ≤ ((∑ stage, quota stage : ℕ) : ℕ∞) := by
    rw [enat_natCast_sum]
    exact Finset.sum_le_sum (fun stage _ => hbound stage)
  have hcommitments : s.ledger.commitments.length ≤ I.toolCount := by
    have hh := hwf.commitment_tools.length_le_card
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hh
  have hexecutions : s.ledger.executions.length ≤ I.toolCount :=
    (Ledger.execution_count_le hwf).trans (min_le_right _ _)
  have hwritten : (writtenPorts s.ledger).card ≤ I.stageCount := by
    have hh := Finset.card_le_card (Finset.filter_subset (fun stage : I.Stage => s.ledger.written stage ≠ none) Finset.univ)
    simpa only [writtenPorts, Finset.card_univ, Instance.Stage, Instance.stageCount, Fintype.card_fin] using hh
  have hhalted : (if s.halted then (1 : ℕ∞) else 0) ≤ 1 := by
    cases s.halted <;> simp
  have ht := add_le_add
    (add_le_add
      (add_le_add
        (add_le_add (add_le_add hreviews (ENat.natCast_le_natCast.mpr hcommitments))
          (ENat.natCast_le_natCast.mpr hexecutions))
        (ENat.natCast_le_natCast.mpr hcursor))
      (ENat.natCast_le_natCast.mpr hwritten)) hhalted
  have hprogress : actionProgress s ≤ (reviewBoundedActionBound I quota : ℕ∞) := by
    simpa only [actionProgress, reviewBoundedActionBound, ENat.natCast_add, ENat.natCast_one] using ht
  rw [prefix_actionProgress input C mode accounting rule seed truth tapes hp] at hprogress
  exact ENat.natCast_le_natCast.mp hprogress

private theorem prefix_eq_run_sample {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (sample : Seed × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) n s) : run input C .uncapped accounting rule sample n = s := by
  have he := prefix_eq_run input C .uncapped accounting rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hw : replayWorld input (input.truthAt sample.2) (worldTapes input sample.2) = sample.2 := rfl
  simpa only [hw] using he

/-- If all actual local review-request counts are bounded on one sample,
the ideal reference halts on that sample. No deterministic uniform review
bound or future-success restriction is supplied. -/
theorem referenceRun_halts_of_not_infinite_reviews
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (sample : Unit × input.World)
    (hfinite : ∀ stage : I.Stage,
      sample ∉ referenceStageInfiniteReviews input C hearly accounting available budget stage) :
    ∃ n, (run input C .uncapped accounting (referenceRule input available budget none) sample n).halted = true := by
  classical
  have hthreshold : ∀ stage : I.Stage, ∃ threshold : ℕ,
      sample ∉ referenceStageOverflow input C hearly accounting available budget (fun _ => threshold) stage := by
    intro stage
    by_contra h
    apply hfinite stage
    intro threshold
    exact not_not.mp (not_exists.mp h threshold)
  choose quota hquota using hthreshold
  have hgate : ∀ (n : ℕ) (s : State I),
      Prefix input C .uncapped accounting (referenceRule input available budget none) sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) n s → s.halted = false →
      ∀ stage : I.Stage, referenceRule input available budget none sample.1 s.history = .review stage →
        s.ledger.reviews stage < (quota stage : ℕ∞) := by
    intro n s hp hactive stage haction
    by_contra hnot
    have hcount : (quota stage : ℕ∞) ≤ s.ledger.reviews stage := le_of_not_gt hnot
    apply hquota stage
    have hrun := prefix_eq_run_sample input C accounting (referenceRule input available budget none) sample hp
    have hunit : sample.1 = () := Subsingleton.elim _ _
    refine ⟨n, ?_⟩
    simpa only [referenceIdealPolicy, referenceUncappedPolicy, hrun] using
      (show s.halted = false ∧ referenceRule input available budget none () s.history = .review stage ∧
        ((fun _ : I.Stage => quota stage) stage : ℕ∞) ≤ s.ledger.reviews stage from
        ⟨hactive, by simpa only [hunit] using haction, hcount⟩)
  by_contra hnever
  let bound := reviewBoundedActionBound I quota
  have hactive : (run input C .uncapped accounting (referenceRule input available budget none) sample (bound + 1)).halted = false :=
    Bool.eq_false_iff.mpr (not_exists.mp hnever (bound + 1))
  have hp := run_prefix_of_active input C .uncapped accounting (referenceRule input available budget none)
    (referenceRule_uncapped_legal input C hearly accounting available budget none) sample (bound + 1) hactive
  have hb := prefix_reviews_le_of_review_gate input C .uncapped accounting (referenceRule input available budget none)
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) quota hgate hp
  have hn := prefix_length_le_of_reviews_bounded input C .uncapped accounting (referenceRule input available budget none)
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp quota hb
  omega

/-- Every nonhalting ideal reference sample has some genuinely unbounded
local review stream. This is a real-path statement with no measure premise. -/
theorem referenceRun_nonhalting_has_infinite_reviews
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (sample : Unit × input.World)
    (hnever : ¬ ∃ n, (run input C .uncapped accounting (referenceRule input available budget none) sample n).halted = true) :
    ∃ stage : I.Stage, sample ∈ referenceStageInfiniteReviews input C hearly accounting available budget stage := by
  classical
  by_contra h
  apply hnever
  apply referenceRun_halts_of_not_infinite_reviews input C hearly accounting available budget sample
  exact not_exists.mp h

/-- Actual uncapped ideal-reference termination is almost sure for every
initial availability and original valid rational risk. Local finite ET and
the real execution identification are the only probability inputs. -/
theorem referenceRun_ae_halts
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    ∀ᵐ sample ∂input.seededWorldLaw (Measure.dirac ()),
      ∃ n, (run input C .uncapped accounting (referenceRule input available budget none) sample n).halted = true := by
  have hlocal : ∀ stage : I.Stage,
      ∀ᵐ sample ∂input.seededWorldLaw (Measure.dirac ()),
        sample ∉ referenceStageInfiniteReviews input C hearly accounting available budget stage := by
    intro stage
    apply ae_iff.mpr
    have heq : {sample : Unit × input.World |
        ¬ sample ∉ referenceStageInfiniteReviews input C hearly accounting available budget stage} =
        referenceStageInfiniteReviews input C hearly accounting available budget stage := by
      ext sample
      simp
    rw [heq]
    exact referenceStageInfiniteReviews_measure_zero input C hearly accounting available budget hbudget hsmall stage
  filter_upwards [ae_all_iff.mpr hlocal] with sample hsample
  exact referenceRun_halts_of_not_infinite_reviews input C hearly accounting available budget sample hsample

theorem referenceRun_nontermination_measure_zero
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    input.seededWorldLaw (Measure.dirac ()) {sample : Unit × input.World |
      ¬ ∃ n, (run input C .uncapped accounting (referenceRule input available budget none) sample n).halted = true} = 0 :=
  ae_iff.mp (referenceRun_ae_halts input C hearly accounting available budget hbudget hsmall)

private theorem cursor_of_stage (cache : ReferenceReplayCache I) (stage : I.Stage)
    (hstage : referenceReplayStage I cache = some stage) : historyCursor cache.seen = stage.val := by
  unfold referenceReplayStage at hstage
  split_ifs at hstage with hb
  exact congrArg (fun i : I.Stage => i.val) (Option.some.inj hstage)

private theorem rankCase_noTool_of_repair_none (available : Finset I.Tool) (stage : I.Stage)
    (used : Finset I.Tool) (kind : ReferenceBudgetCase)
    (hcase : referenceAvailableRankCase I available stage used = some kind)
    (hpick : referenceAvailableRepairTool I available stage used = none) : kind = .noTool := by
  have hp : pickGenericMaxRankTool I.toolCount (I.eligible stage)
      (I.compatibility.drop (stage.val + 1)) (available \ used) = none := by
    simpa only [referenceAvailableRepairTool, referenceRepairTool, referenceRank_remaining] using hpick
  have hbad := (badChildRank_eq_zero_iff (I.eligible stage) (I.compatibility.drop (stage.val + 1))
    (available \ used)).mpr ((pickGenericMaxRankTool_eq_none _ _ _ _).mp hp)
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
theorem referenceTestingAction_ideal_ne_abandon {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting rule seed truth tapes n s)
    (available : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I)
    (haligned : ReferenceStateAligned input available budget cache s)
    (hphase : cache.phase = .testing) (hactive : s.halted = false)
    (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    referenceTestingAction input available budget none cache stage ≠ .abandon := by
  obtain ⟨kind, current, hkind, hcurrent, hv, hlen⟩ :=
    referenceStateAligned_testing_ready input available budget cache s haligned hphase stage hcursor
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hword : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize := by
    rw [haligned.seen]
    exact prefix_historyObservation_alphabet input C .uncapped accounting rule seed truth tapes hp stage
  cases kind with
  | infiniteRank => simp [referenceTestingAction, hkind]
  | noTool =>
    have ht : referenceAvailableCacheTarget I available budget cache = some (current / 2) := by
      simp [referenceAvailableCacheTarget, hh, hphase, hkind, hcurrent,
        hv.1, Nat.le_of_lt hlen, referenceBudgetTarget]
      simpa only [one_div] using hv.2
    simp only [referenceTestingAction, hkind, ht, dite_eq_left hword]
    split_ifs <;> simp
  | finiteBad depth =>
    have ht : referenceAvailableCacheTarget I available budget cache = some (controllerTarget current depth.val) := by
      simp [referenceAvailableCacheTarget, hh, hphase, hkind, hcurrent,
        hv.1, Nat.le_of_lt hlen, referenceBudgetTarget]
      simpa only [one_div] using hv.2
    simp only [referenceTestingAction, hkind, ht, dite_eq_left hword]
    split_ifs <;> simp

/-- Actual ideal abandonment can occur only immediately after a reported
no-tool error. Parser/ledger alignment is derived from the actual Prefix,
and the wrong ordinary bit is read from the actual ledger. -/
theorem referenceRule_abandon_noTool_error {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget none) seed truth tapes n s)
    (hactive : s.halted = false)
    (haction : referenceRule input available budget none seed s.history = .abandon) :
    ∃ (stage : I.Stage) (cache : ReferenceReplayCache I),
      ReferenceStateAligned input available budget cache s ∧ s.cursor = stage.val ∧
      cache.phase = .reported ∧ referenceReplayCorrect cache stage = false ∧
      referenceAvailableKind I available cache = some .noTool ∧
      s.ledger.written stage = some (!s.ledger.truth stage) := by
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget
    hbudget hsmall none seed truth tapes hp
  have hh : cache.halted = false := haligned.halted.trans hactive
  have ha : referenceCandidateAction input available budget none s.history = .abandon :=
    (referenceRule_eq_candidate_of_prefix input C hearly accounting available budget hbudget hsmall none
      seed truth tapes hp).symm.trans haction
  cases hstage : referenceReplayStage I cache with
  | none =>
    have hb := (prefix_cursorInvariant input C .uncapped accounting
      (referenceRule input available budget none) seed truth tapes hp).bound
    have hnot : ¬ historyCursor cache.seen < I.stageCount := by
      intro h
      simp [referenceReplayStage, h] at hstage
    have hcursor : historyCursor s.history = I.stageCount := by
      rw [← haligned.seen, haligned.cursor]
      rw [haligned.cursor] at hnot
      omega
    simp [referenceCandidateAction, haligned.parsed, hh, hstage, hcursor] at ha
  | some stage =>
    have hc : s.cursor = stage.val := haligned.cursor.symm.trans (cursor_of_stage cache stage hstage)
    cases hphase : cache.phase with
    | testing =>
      have ht : referenceTestingAction input available budget none cache stage = .abandon := by
        simpa only [referenceCandidateAction, haligned.parsed, hh, Bool.false_eq_true, ite_false, hstage, hphase] using ha
      exact (referenceTestingAction_ideal_ne_abandon input C accounting (referenceRule input available budget none)
        seed truth tapes hp available budget cache haligned hphase hactive stage hc ht).elim
    | written => exact ((referenceAvailableReplay_some_spec input available budget s.history cache haligned.parsed).2.2.1 hphase).elim
    | reported =>
      have hf := haligned.current_fields stage hc
      simp only [referenceCurrentLedgerFits, hphase] at hf
      obtain ⟨bit, hwritten⟩ := Option.ne_none_iff_exists'.mp hf.1
      have hw := prefix_historyWrite input C .uncapped accounting (referenceRule input available budget none)
        seed truth tapes hp stage
      rw [hwritten] at hw
      let handle : MismatchHandle I := ⟨stage, s.ledger.writeSerial stage⟩
      have hvisible : referenceVisibleHandle s.history stage = some handle := by
        simp [referenceVisibleHandle, hw, handle]
      cases hcorrect : referenceReplayCorrect cache stage with
      | true => simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hcorrect] at ha
      | false =>
        obtain ⟨kind, entryRisk, hkind, _, hupdate⟩ := haligned.reported_update
          (by simp [hphase, referencePhaseReportCount]) stage hc
        have hcase : referenceAvailableRankCase I available stage (historyUsed cache.entryHistory) = some kind := by
          simpa only [referenceAvailableKind, hstage, Option.bind_eq_bind, Option.bind_some] using hkind
        have hkindNoTool : kind = .noTool := by
          cases hrisk : referenceReplayRisk budget cache with
          | none =>
            rw [hrisk, hcorrect] at hupdate
            cases kind <;> simp [referenceBudgetStep] at hupdate ⊢
          | some current =>
            cases hpick : referenceAvailableRepairTool I available stage (historyUsed cache.entryHistory) with
            | none => exact rankCase_noTool_of_repair_none available stage (historyUsed cache.entryHistory) kind hcase hpick
            | some tool =>
              simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hcorrect, hrisk, hvisible, hpick] at ha
        have hvalid := (referenceStateAligned_reported_mismatch input C hearly accounting
          (referenceRule input available budget none) seed truth tapes hp available budget cache haligned
          hphase stage hc hcorrect handle hvisible).1
        refine ⟨stage, cache, haligned, hc, hphase, hcorrect, ?_, ?_⟩
        · simpa only [hkindNoTool] using hkind
        · exact hvalid.1
    | allocated tool =>
      obtain ⟨handle, hs, hvalid, _, _, _, _⟩ := by
        simpa only [referenceCurrentLedgerFits, hphase] using haligned.current_fields stage hc
      have hvisible := prefix_visibleHandle_of_valid input C hearly .uncapped accounting
        (referenceRule input available budget none) seed truth tapes hp handle hvalid
      rw [hs] at hvisible
      simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hvisible] at ha
    | executed tool => simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase] at ha

/-- A real ideal-reference stop is successful for every initial available
set, including finite rank. Abandonment is a different, explicit action. -/
theorem referenceRule_stop_success {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget none) seed truth tapes n s)
    (hactive : s.halted = false)
    (haction : referenceRule input available budget none seed s.history = .stop) :
    (stopState s false).ledger.success C := by
  classical
  have hpnext : Prefix input C .uncapped accounting (referenceRule input available budget none)
      seed truth tapes (n + 1) (stopState s false) := .next hp (haction ▸ .stop s hactive)
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget
    hbudget hsmall none seed truth tapes hp
  obtain ⟨nextCache, hnextAligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget
    hbudget hsmall none seed truth tapes hpnext
  have hs := referenceAvailableReplay_some_spec input available budget s.history cache haligned.parsed
  have hs' := referenceAvailableReplay_some_spec input available budget (s.history ++ [.stopped]) nextCache hnextAligned.parsed
  rw [List.foldlM_append, hs.2.1] at hs'
  have hsingle : referenceAvailableStep input available budget cache .stopped = some nextCache := by
    simpa using hs'.2.1
  have hh : cache.halted = false := haligned.halted.trans hactive
  simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hsingle
  obtain ⟨hg, _⟩ := some_if_some _ _ _ hsingle
  have hcursor : s.cursor = I.stageCount := haligned.cursor.symm.trans hg.1
  have hcorrect (stage : I.Stage) : s.ledger.written stage = some (s.ledger.truth stage) ∨
      ∃ e ∈ s.ledger.executions, e.handle.stage = stage :=
    prefix_reference_pastCorrect input C hearly accounting available budget hbudget hsmall none
      seed truth tapes hp stage (hcursor ▸ stage.isLt)
  have hwf := prefix_ledgerWellFormed input C .uncapped accounting
    (referenceRule input available budget none) seed truth tapes hp
  have hall : allWritten s.ledger := by
    intro stage
    rcases hcorrect stage with hw | ⟨e, he, hs⟩
    · rw [hw]; simp
    · have hg := (hwf.genuine e he).1
      rw [hs] at hg
      rw [hg]; simp
  apply (prefix_success_iff_physical input C .uncapped accounting
    (referenceRule input available budget none) seed truth tapes hpnext).mpr
  refine ⟨?_, rfl, ?_⟩
  · change decide (allWritten s.ledger) = true
    exact decide_eq_true hall
  · intro stage
    exact (finalOutput_correct_iff _ stage).mpr (hcorrect stage)

/-- A finite-stage failure source in the real ideal run. The report and
ordinary error are actual ledger data, and rank uses the original entry
availability snapshot. No successful-future conditioning is present. -/
def referenceStageNoToolFailure (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) :
    Set (Unit × input.World) :=
  {sample | ∃ (n : ℕ) (cache : ReferenceReplayCache I),
    let s := run input C .uncapped accounting (referenceRule input available budget none) sample n
    s.halted = false ∧ s.cursor = stage.val ∧
      referenceRule input available budget none sample.1 s.history = .abandon ∧
      referenceAvailableReplay input available budget s.history = some cache ∧
      cache.phase = .reported ∧ referenceReplayCorrect cache stage = false ∧
      referenceAvailableKind I available cache = some .noTool ∧
      s.ledger.written stage = some (!s.ledger.truth stage)}

private theorem prefix_halted_success_or_noToolFailure
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget none)
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n s) (hhalt : s.halted = true) :
    s.ledger.success C ∨ ∃ stage : I.Stage,
      sample ∈ referenceStageNoToolFailure input C accounting available budget stage := by
  cases hp with
  | initial => cases hhalt
  | @next n s next earlier step =>
    generalize haction : referenceRule input available budget none sample.1 s.history = action at step
    cases step with
    | review current live port resources => cases hhalt
    | write current bit live port resources => cases hhalt
    | allocate handle tool active valid compatible unused unallocated window resources => cases hhalt
    | execute handle tool active valid compatible committed unused uncorrected window resources => cases hhalt
    | advance stage live written resources => cases hhalt
    | stop active =>
      exact Or.inl (referenceRule_stop_success input C hearly accounting available budget hbudget hsmall
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier active haction)
    | abandon active =>
      obtain ⟨stage, cache, haligned, hcursor, hphase, hcorrect, hkind, hwrong⟩ :=
        referenceRule_abandon_noTool_error input C hearly accounting available budget hbudget hsmall
          sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier active haction
      refine Or.inr ⟨stage, n, cache, ?_⟩
      rw [prefix_eq_run_sample input C accounting (referenceRule input available budget none) sample earlier]
      exact ⟨active, hcursor, haction, haligned.parsed, hphase, hcorrect, hkind, hwrong⟩

/-- Every actual failed ideal run either does not halt or has a finite
reported no-tool error. The first alternative is already a proved null set. -/
theorem referenceFailure_subset_nontermination_union_noTool
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    {sample : Unit × input.World |
      ¬ runSuccess input C .uncapped accounting (referenceRule input available budget none) sample} ⊆
    {sample : Unit × input.World | ¬ ∃ n,
      (run input C .uncapped accounting (referenceRule input available budget none) sample n).halted = true} ∪
      ⋃ stage : I.Stage, referenceStageNoToolFailure input C accounting available budget stage := by
  intro sample hfailure
  by_cases hhalt : ∃ n, (run input C .uncapped accounting (referenceRule input available budget none) sample n).halted = true
  · obtain ⟨n, hh⟩ := hhalt
    obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (referenceRule input available budget none)
      (referenceRule_uncapped_legal input C hearly accounting available budget none) sample n
    rcases prefix_halted_success_or_noToolFailure input C hearly accounting available budget hbudget hsmall sample hp hh with
      hsuccess | ⟨stage, hstage⟩
    · exact (hfailure ⟨n, hh, hsuccess⟩).elim
    · exact Or.inr (Set.mem_iUnion.mpr ⟨stage, hstage⟩)
  · exact Or.inl hhalt

theorem referenceRisk_le_sum_noToolFailure
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) :
    risk input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      ∑ stage : I.Stage, input.seededWorldLaw (Measure.dirac ())
        (referenceStageNoToolFailure input C accounting available budget stage) := by
  calc
    _ ≤ input.seededWorldLaw (Measure.dirac ())
        ({sample : Unit × input.World | ¬ ∃ n,
          (run input C .uncapped accounting (referenceRule input available budget none) sample n).halted = true} ∪
            ⋃ stage : I.Stage, referenceStageNoToolFailure input C accounting available budget stage) :=
      measure_mono (referenceFailure_subset_nontermination_union_noTool input C hearly accounting available budget hbudget hsmall)
    _ ≤ input.seededWorldLaw (Measure.dirac ()) {sample : Unit × input.World | ¬ ∃ n,
          (run input C .uncapped accounting (referenceRule input available budget none) sample n).halted = true} +
        input.seededWorldLaw (Measure.dirac ()) (⋃ stage : I.Stage, referenceStageNoToolFailure input C accounting available budget stage) :=
      measure_union_le _ _
    _ ≤ 0 + ∑ stage : I.Stage, input.seededWorldLaw (Measure.dirac ())
        (referenceStageNoToolFailure input C accounting available budget stage) := by
      rw [referenceRun_nontermination_measure_zero input C hearly accounting available budget hbudget hsmall]
      simpa only [zero_add, tsum_fintype] using
        (measure_iUnion_le (μ := input.seededWorldLaw (Measure.dirac ()))
          (fun stage : I.Stage => referenceStageNoToolFailure input C accounting available budget stage))
    _ = _ := zero_add _

end PaperProofs.Common.Native
