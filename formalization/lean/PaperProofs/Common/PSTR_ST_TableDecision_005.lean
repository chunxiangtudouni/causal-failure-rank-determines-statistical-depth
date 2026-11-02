module

public import PaperProofs.Common.PSTR_ST_TableOrigin_004
public import PaperProofs.Common.ReferenceDecisionRealization

/-! Real finite-target writes and local error/null-tail measures for the
actual table tie. No generic/table equality of paths, bills or risk is used. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.TableDecision

open PaperProofs.Statistics PaperProofs.Structure CompactPrice TableAlignment TableOrigin
open PaperProofs.Structure.LaminarTree

variable {I : Instance}

abbrev tableIdealPolicy (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) : Policy input C .uncapped accounting Unit :=
  tableUncappedPolicy input C hearly accounting available budget none

theorem tableEntryTarget_valid (input : StatisticalInput I) (available : Finset I.Tool)
    (budget p : ℚ) (history : List (VisibleEvent I))
    (htarget : tableEntryTarget input available budget history = some p) : 0 < p ∧ p ≤ 1 / 4 := by
  obtain ⟨cache, _, ht⟩ := Option.bind_eq_some_iff.mp htarget
  obtain ⟨kind, current, _, _, hv, _, hb⟩ := tableTarget_some_spec I available budget p cache ht
  have hp := referenceBudgetTarget_valid_floor kind current p hv hb
  exact ⟨hp.1, hp.2.1⟩

private theorem cacheTarget_bounds (I : Instance) (available : Finset I.Tool) (budget p : ℚ)
    (cache : ReferenceReplayCache I) (ht : tableTarget I available budget cache = some p) : 0 < p ∧ p < 1 := by
  obtain ⟨kind, current, _, _, hv, _, hb⟩ := tableTarget_some_spec I available budget p cache ht
  have hp := referenceBudgetTarget_valid_floor kind current p hv hb
  exact ⟨hp.1, lt_of_le_of_lt hp.2.1 (by norm_num)⟩

def tableStageOverflow (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ) (stage : I.Stage) :
    Set (Unit × input.World) :=
  {sample | ∃ n : ℕ,
    let state := run input C .uncapped accounting
      (tableIdealPolicy input C hearly accounting available budget).rule sample n
    state.halted = false ∧
    (tableIdealPolicy input C hearly accounting available budget).rule () state.history = .review stage ∧
    (quota stage : ℕ∞) ≤ state.ledger.reviews stage}

private theorem candidate_write_testing (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (hparse : tableReplay input available budget history = some cache)
    (stage : I.Stage) (bit : Bool)
    (haction : tableCandidate input available budget none history = .write stage bit) :
    cache.phase = .testing ∧ referenceReplayStage I cache = some stage ∧
      tableTestingAction input available budget none cache stage = .write stage bit := by
  cases hh : cache.halted with
  | true => simp [tableCandidate, hparse, hh] at haction
  | false =>
    cases hs : referenceReplayStage I cache with
    | none =>
      simp only [tableCandidate, hparse, hh, Bool.false_eq_true, ite_false, hs] at haction
      split_ifs at haction
    | some current =>
      cases hphase : cache.phase with
      | testing =>
        have ht : tableTestingAction input available budget none cache current = .write stage bit := by
          simpa only [tableCandidate, hparse, hh, Bool.false_eq_true, ite_false, hs, hphase] using haction
        rcases tableTestingAction_supported input available budget none cache current with hreview | ⟨otherBit, hwrite⟩ | habandon
        · rw [hreview] at ht
          cases ht
        · have heq := (Action.write.inj (hwrite.symm.trans ht)).1
          subst current
          exact ⟨rfl, rfl, ht⟩
        · rw [habandon] at ht
          cases ht
      | written => simp [tableCandidate, hparse, hh, hs, hphase] at haction
      | executed tool => simp [tableCandidate, hparse, hh, hs, hphase] at haction
      | allocated tool =>
        cases hv : referenceVisibleHandle history current <;> simp [tableCandidate, hparse, hh, hs, hphase, hv] at haction
      | reported =>
        cases hc : referenceReplayCorrect cache current with
        | true => simp [tableCandidate, hparse, hh, hs, hphase, hc] at haction
        | false =>
          cases hr : referenceReplayRisk budget cache with
          | none => simp [tableCandidate, hparse, hh, hs, hphase, hc, hr] at haction
          | some currentRisk =>
            cases hv : referenceVisibleHandle history current with
            | none => simp [tableCandidate, hparse, hh, hs, hphase, hc, hr, hv] at haction
            | some handle =>
              cases ht : tableRepairTool I available current (historyUsed cache.entryHistory) <;>
                simp [tableCandidate, hparse, hh, hs, hphase, hc, hr, hv, ht] at haction

theorem tableTestingAction_posteriorWrite_hit (input : StatisticalInput I) (available : Finset I.Tool)
    (budget p : ℚ) (cache : ReferenceReplayCache I) (stage : I.Stage) (bit : Bool)
    (htarget : tableTarget I available budget cache = some p)
    (hvalid : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize)
    (haction : tableTestingAction input available budget none cache stage = .write stage bit) :
    (input.experiment stage).rationalWordHits p (historyObservationWord input cache.seen stage hvalid) = true ∧
      bit = (input.experiment stage).rationalWordMAP (historyObservationWord input cache.seen stage hvalid) := by
  obtain ⟨kind, current, hk, _, _, _, hb⟩ := tableTarget_some_spec I available budget p cache htarget
  cases kind with
  | infiniteRank => cases hb
  | noTool | finiteBad depth =>
    simp only [tableTestingAction, hk, htarget, dite_eq_left hvalid] at haction
    cases hh : (input.experiment stage).rationalWordHits p (historyObservationWord input cache.seen stage hvalid) with
    | false => simp only [hh, Bool.false_eq_true, ite_false] at haction; cases haction
    | true =>
      simp only [hh, ite_true] at haction
      exact ⟨rfl, (Action.write.inj haction).2.symm⟩

private theorem cursor_of_replayStage (cache : ReferenceReplayCache I) (stage : I.Stage)
    (hstage : referenceReplayStage I cache = some stage) : historyCursor cache.seen = stage.val := by
  unfold referenceReplayStage at hstage
  split_ifs at hstage
  exact congrArg (fun i : I.Stage => i.val) (Option.some.inj hstage)

/-- Every actual finite-target ideal write occurs at exactly the selected
SPRT stopping time, and writes its actual MAP decision. The initial
available set is unrestricted; the table policy retains its original Unit seed. -/
theorem prefix_tablePosteriorWrite_realization  (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s)
    (hactive : s.halted = false) (stage : I.Stage) (bit : Bool)
    (haction : tableRule input available budget none sample.1 s.history = .write stage bit)
    (history : List (VisibleEvent I)) (p : ℚ)
    (hentry : entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history)
    (htarget : tableEntryTarget input available budget history = some p) :
    (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 = ((s.ledger.reviews stage).toNat : ℕ∞) ∧
      bit = ((input.experiment stage).posteriorSPRT p).rule.decision () (sample.2 stage).2 := by
  obtain ⟨cache, haligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hcand := (tableRule_eq_candidate_of_prefix hlaminar input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp).symm.trans haction
  obtain ⟨hphase, hstage, htest⟩ := candidate_write_testing input available budget s.history cache haligned.parsed stage bit hcand
  have hcursor := haligned.cursor.symm.trans (cursor_of_replayStage cache stage hstage)
  obtain ⟨origin, he, _, ht, hprogress⟩ := prefix_tableTesting_origin input hlaminar C hearly accounting available budget hbudget hsmall sample
    hp cache haligned hactive hphase stage hcursor
  have heq : origin = history := Option.some.inj (he.symm.trans hentry)
  rw [heq] at ht
  have hpCache : tableTarget I available budget cache = some p := ht.symm.trans htarget
  have hb := cacheTarget_bounds I available budget p cache hpCache
  have hvalid : ∀ symbol ∈ historyObservations s.history stage, symbol < (input.experiment stage).alphabetSize :=
    fun symbol hm => prefix_historyObservation_alphabet input C .uncapped accounting
      (tableRule input available budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage symbol hm
  have hvalidCache : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize := by
    simpa only [haligned.seen] using hvalid
  obtain ⟨hhit, hbit⟩ := tableTestingAction_posteriorWrite_hit input available budget p cache stage bit hpCache hvalidCache htest
  have hhit' : (input.experiment stage).rationalWordHits p (historyObservationWord input s.history stage hvalid) = true := by
    simpa only [haligned.seen] using hhit
  have hbit' : bit = (input.experiment stage).rationalWordMAP (historyObservationWord input s.history stage hvalid) := by
    simpa only [haligned.seen] using hbit
  have hboundary := (prefix_historyObservationWord_hits_iff input C .uncapped accounting
    (tableRule input available budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage hvalid p hb.1 hb.2).mp hhit'
  have hle := ((input.experiment stage).posteriorThresholdStop_le_iff p (worldTapes input sample.2 stage) (s.ledger.reviews stage).toNat).mpr
    ⟨_, le_rfl, hboundary⟩
  have hfinite := prefix_reviews_natCast_toNat input C .uncapped accounting (tableRule input available budget none)
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage
  have hw : worldTapes input sample.2 stage = (sample.2 stage).2 := by funext k; rfl
  have hge : ((s.ledger.reviews stage).toNat : ℕ∞) ≤
      (input.experiment stage).posteriorThresholdStop p (worldTapes input sample.2 stage) := by
    rw [hfinite, hw]
    exact hprogress p hpCache
  have hstop := le_antisymm hle hge
  refine ⟨by simpa only [hw] using hstop, ?_⟩
  have hmap := prefix_historyObservationWord_MAP_at_stop input C .uncapped accounting
    (tableRule input available budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage hvalid p hstop
  simpa only [hw] using hbit'.trans hmap

def tableEntryChoice (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ) :
    Unit × List (VisibleEvent I) → Option ℚ := fun sample => tableEntryTarget input available budget sample.2

theorem measurable_tableEntryChoice (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ) :
    Measurable (tableEntryChoice input available budget) := measurable_of_countable _

/-- A genuine wrong write on a branch whose genuine entry chose a posterior
test. Infinite-rank blind writes are deliberately a separate structural case. -/
def tableStagePosteriorError (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) : Set (Unit × input.World) :=
  {sample | ∃ (n : ℕ) (bit : Bool) (history : List (VisibleEvent I)) (p : ℚ),
    let state := run input C .uncapped accounting (tableIdealPolicy input C hearly accounting available budget).rule sample n
    state.halted = false ∧
    (tableIdealPolicy input C hearly accounting available budget).rule () state.history = .write stage bit ∧
    entryHistory input C .uncapped accounting (tableIdealPolicy input C hearly accounting available budget).rule stage sample = some history ∧
    tableEntryTarget input available budget history = some p ∧ bit ≠ (sample.2 stage).1}

theorem tableStagePosteriorError_subset_entryPosteriorError (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    tableStagePosteriorError input C hearly accounting available budget stage ⊆
      entryPosteriorError input C .uncapped accounting (tableIdealPolicy input C hearly accounting available budget).rule
        stage (tableEntryChoice input available budget) := by
  rintro ⟨⟨⟩, world⟩ ⟨n, bit, history, p, hactive, hwrite, hentry, htarget, hwrong⟩
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (tableIdealPolicy input C hearly accounting available budget).rule
    (tableIdealPolicy input C hearly accounting available budget).legal ((), world) n
  have hreal := prefix_tablePosteriorWrite_realization input hlaminar C hearly accounting available budget hbudget hsmall ((), world)
    hp hactive stage bit hwrite history p hentry htarget
  refine ⟨p, ?_, ?_⟩
  · change entryGatedTarget (tableEntryChoice input available budget)
      ((), entryHistory input C .uncapped accounting (tableRule input available budget none) stage ((), world)) = some p
    have he : entryHistory input C .uncapped accounting (tableRule input available budget none) stage ((), world) = some history := hentry
    rw [he]
    exact htarget
  · change ((input.experiment stage).posteriorSPRT p).rule.decision () (world stage).2 ≠ (world stage).1
    rw [← hreal.2]
    exact hwrong

theorem tableStagePosteriorError_measure_le (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ()) (tableStagePosteriorError input C hearly accounting available budget stage) ≤
      ∫⁻ sample, selectedTargetBound (entryGatedTarget (tableEntryChoice input available budget))
        (entrySeedHistory input C .uncapped accounting (tableIdealPolicy input C hearly accounting available budget).rule stage sample)
          ∂input.seededWorldLaw (Measure.dirac ()) := by
  apply (measure_mono (tableStagePosteriorError_subset_entryPosteriorError input hlaminar C hearly accounting available budget hbudget hsmall stage)).trans
  exact entryPosteriorError_le input C .uncapped accounting (tableIdealPolicy input C hearly accounting available budget)
    (Measure.dirac ()) stage (tableEntryChoice input available budget)
    (measurable_tableEntryChoice input available budget)
    (fun _ history p hp => tableEntryTarget_valid input available budget p history hp)

/-- A true per-entry error bound, stated by multiplication so null entry
histories are included. The joint law is the proved pre-birth product law,
not an assumed Markov property or a full-state private seed. -/
theorem tableStagePosteriorError_on_entry_le (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : tableEntryTarget input available budget history = some p) :
    input.seededWorldLaw (Measure.dirac ())
        (tableStagePosteriorError input C hearly accounting available budget stage ∩
          {sample | entryHistory input C .uncapped accounting (tableIdealPolicy input C hearly accounting available budget).rule
            stage sample = some history}) ≤
      ENNReal.ofReal (p : ℝ) * input.seededWorldLaw (Measure.dirac ())
        {sample | entryHistory input C .uncapped accounting (tableIdealPolicy input C hearly accounting available budget).rule
          stage sample = some history} := by
  let policy := tableIdealPolicy input C hearly accounting available budget
  let μ := input.seededWorldLaw (Measure.dirac ())
  let record := entrySeedHistory input C .uncapped accounting policy.rule stage
  let joint := fun sample : Unit × input.World => (record sample, sample.2 stage)
  let rectangle : Set ((Unit × EntryHistory I) × input.StageSample stage) :=
    {((), some history)} ×ˢ fixedPosteriorError input stage p
  have hrecord : Measurable record := measurable_entrySeedHistory input C .uncapped accounting policy.rule policy.measurable_rule stage
  have hjoint : Measurable joint := hrecord.prodMk ((measurable_pi_apply stage).comp measurable_snd)
  have hrectangle : MeasurableSet rectangle := (measurableSet_singleton _).prod (measurableSet_fixedPosteriorError input stage p)
  have hsubset : tableStagePosteriorError input C hearly accounting available budget stage ∩
      {sample | entryHistory input C .uncapped accounting policy.rule stage sample = some history} ⊆ joint ⁻¹' rectangle := by
    intro sample hs
    obtain ⟨q, hq, herror⟩ := tableStagePosteriorError_subset_entryPosteriorError input hlaminar C hearly accounting available budget hbudget hsmall stage hs.1
    have he : entryHistory input C .uncapped accounting policy.rule stage sample = some history := hs.2
    have hq' : tableEntryTarget input available budget history = some q := by
      change entryGatedTarget (tableEntryChoice input available budget)
        (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) = some q at hq
      rw [he] at hq
      exact hq
    have hqp : q = p := Option.some.inj (hq'.symm.trans htarget)
    subst q
    refine ⟨?_, herror⟩
    change (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) ∈ {((), some history)}
    rw [he]
    cases sample.1
    exact Set.mem_singleton _
  have hmass : (μ.map record) {((), some history)} = μ
      {sample | entryHistory input C .uncapped accounting policy.rule stage sample = some history} := by
    rw [Measure.map_apply hrecord (measurableSet_singleton _)]
    congr 1
    ext sample
    change (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) = ((), some history) ↔ _
    cases sample.1
    simp only [Prod.mk.injEq, true_and, Set.mem_ofPred_eq]
  have hp := tableEntryTarget_valid input available budget p history htarget
  calc
    μ (tableStagePosteriorError input C hearly accounting available budget stage ∩
        {sample | entryHistory input C .uncapped accounting policy.rule stage sample = some history})
      ≤ μ (joint ⁻¹' rectangle) := measure_mono hsubset
    _ = (μ.map joint) rectangle := (Measure.map_apply hjoint hrectangle).symm
    _ = ((μ.map record).prod (input.stageLaw stage)) rectangle := by
      rw [entrySeedHistory_jointLaw input C .uncapped accounting policy (Measure.dirac ()) stage]
    _ = (μ.map record) {((), some history)} * input.stageLaw stage (fixedPosteriorError input stage p) := Measure.prod_prod _ _
    _ ≤ (μ.map record) {((), some history)} * ENNReal.ofReal (p : ℝ) :=
      mul_le_mul_right (stageLaw_fixedPosteriorError_le input stage p hp.1 hp.2) _
    _ = ENNReal.ofReal (p : ℝ) * μ
        {sample | entryHistory input C .uncapped accounting policy.rule stage sample = some history} := by
      rw [hmass, mul_comm]

/-- The actual interpreter requests reviews on this stage with unbounded
sample count. All witnesses are genuine active returned-action states. -/
def tableStageInfiniteReviews (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) : Set (Unit × input.World) :=
  {sample | ∀ threshold : ℕ,
    sample ∈ tableStageOverflow input C hearly accounting available budget (fun _ => threshold) stage}

theorem tableStageInfiniteReviews_realization (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (sample : Unit × input.World) (hinfinite : sample ∈ tableStageInfiniteReviews input C hearly accounting available budget stage) :
    ∃ history : List (VisibleEvent I), ∃ p : ℚ,
      entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history ∧
      tableEntryTarget input available budget history = some p ∧
      (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 = ⊤ := by
  rcases sample with ⟨⟨⟩, world⟩
  obtain ⟨n, hactive, hreview, _⟩ := hinfinite 0
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (tableIdealPolicy input C hearly accounting available budget).rule
    (tableIdealPolicy input C hearly accounting available budget).legal ((), world) n
  obtain ⟨history, p, hentry, htarget, _⟩ := prefix_tableReview_realization input hlaminar C hearly accounting available budget hbudget hsmall
    ((), world) hp hactive stage hreview
  refine ⟨history, p, hentry, htarget, ?_⟩
  by_contra hfinite
  let T := (input.experiment stage).posteriorThresholdStop p (world stage).2
  have hcast : (T.toNat : ℕ∞) = T := ENat.natCast_toNat hfinite
  obtain ⟨m, hactive', hreview', hcount⟩ := hinfinite T.toNat
  obtain ⟨_, _, hp'⟩ := run_has_prefix input C .uncapped accounting (tableIdealPolicy input C hearly accounting available budget).rule
    (tableIdealPolicy input C hearly accounting available budget).legal ((), world) m
  obtain ⟨otherHistory, q, hentry', htarget', hstrict⟩ := prefix_tableReview_realization input hlaminar C hearly accounting available budget hbudget hsmall
    ((), world) hp' hactive' stage hreview'
  have heq : otherHistory = history := Option.some.inj (hentry'.symm.trans hentry)
  rw [heq] at htarget'
  have hqp : q = p := Option.some.inj (htarget'.symm.trans htarget)
  subst q
  have hlt : (T.toNat : ℕ∞) < T := hcount.trans_lt hstrict
  rw [hcast] at hlt
  exact (lt_irrefl T) hlt

/-- Genuine local infinite-review paths are null. Finite ET, the exact
stage marginal, and countably many rational entry targets establish this;
no native quota horizon is applied to the uncapped reference. -/
theorem tableStageInfiniteReviews_measure_zero (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ()) (tableStageInfiniteReviews input C hearly accounting available budget stage) = 0 := by
  have hfinite := seededWorld_ae_all_posteriorSPRT_finite input (Measure.dirac ()) stage
  apply measure_mono_null ?_ (ae_iff.mp hfinite)
  intro sample hinfinite hall
  obtain ⟨history, p, _, htarget, hstop⟩ := tableStageInfiniteReviews_realization input hlaminar C hearly accounting available budget hbudget hsmall
    stage sample hinfinite
  have hp := tableEntryTarget_valid input available budget p history htarget
  exact hall p hp.1 hp.2 hstop


end PaperProofs.Common.Native.PSTRStatistics.TableDecision
