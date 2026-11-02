module

public import PaperProofs.Common.HealthyHistoryScope
public import PaperProofs.Common.NativePenaltyHeadLower
public import PaperProofs.Statistics.LocalLower

/-!
A closed rational native counterexample to the literal broad
AllHealthyHistoryPenaltyBridge, not to the proved first-entry bridge.
The positive-mass public record follows the CURRENT ordinary write and early
report. If informal healthy states are intended to exclude current writes,
this result diagnoses an overly broad encoding; it alone does not refute that
unwritten interpretation. HealthyPrewriteCounterexample separately refutes
the after-review, still-unwritten scope. The broad target remains unchanged;
the paper's first-entry amendment was explicitly approved on 2026-10-29.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace PaperProofs.Common.Native.B09Counterexample

open PaperProofs.Statistics

def single : Instance := ⟨0, [∅]⟩

def head : single.Stage := ⟨0, by decide⟩

def input (E : BinaryExperiment) : StatisticalInput single where
  experiment := fun _ => E
  correctionFee := fun _ tool => Fin.elim0 tool
  correctionFee_nonneg := fun _ tool => Fin.elim0 tool

theorem exists_positive_localValue (E : BinaryExperiment) :
    ∃ price : ℝ, 0 < price ∧ 0 < E.localValueReal price := by
  have hbound := E.localValue_ratio_eventually_ge (1 / 2) (by norm_num)
  obtain ⟨price, hp, hb⟩ := ((eventually_gt_atTop (1 : ℝ)).and hbound).exists
  refine ⟨price, lt_trans zero_lt_one hp, ?_⟩
  have hd : 0 < E.coefficient * Real.log price :=
    mul_pos E.coefficient_pos (Real.log_pos hp)
  have h := (le_div_iff₀ hd).mp hb
  exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 1 - 1 / 2) hd) h

theorem exists_positive_freshPenalty (E : BinaryExperiment) :
    ∃ price : ℝ, 0 < price ∧
      0 < (input E).healthyPenalty 0 ∅ (ENNReal.ofReal price) := by
  obtain ⟨price, hp, hj⟩ := exists_positive_localValue E
  have hg : (input E).goodPenaltyReal head ∅ price = 0 := by
    unfold StatisticalInput.goodPenaltyReal
    exact (input E).healthyPenaltyReal_terminal 1 (by decide) ∅ price
  have hb : (input E).badPenaltyReal head ∅ price = price := by
    simp [StatisticalInput.badPenaltyReal]
  have hl := currentPenaltyRecursion_lower (input E) head ∅ price hp
  rw [hg, hb, sub_zero, zero_add] at hl
  have hr : 0 < (input E).healthyPenaltyReal 0 ∅ price :=
    lt_of_lt_of_le (lt_min hp hj) hl
  refine ⟨price, hp, ?_⟩
  by_contra hn
  have hz : (input E).healthyPenalty 0 ∅ (ENNReal.ofReal price) = 0 :=
    le_antisymm (le_of_not_gt hn) zero_le
  simp only [StatisticalInput.healthyPenaltyReal, hz, ENNReal.toReal_zero,
    lt_self_iff_false] at hr

def contract : Contract single := ⟨.early, .currentWindow, .terminalBarrier, fun _ => 0, 0, 0⟩

def rule : PolicyRule single Unit := fun _ history =>
  if history = [] then .write head false else .stop

noncomputable def writtenState (_E : BinaryExperiment) (truth : single.Stage → Bool) : State single :=
  record (zeroNormalAccounting single) (initial truth) (.write head false)
    (writeResponses contract (initial truth) head false)
    (reportedWriteLedger contract (initial truth) head false) 0 false

theorem write_step (E : BinaryExperiment) (truth : single.Stage → Bool)
    (tapes : ReviewTapes (input E)) :
    Step (input E) contract .native (zeroNormalAccounting single) tapes
      (initial truth) (.write head false) (writtenState E truth) := by
  apply Step.write
  · exact ⟨rfl, rfl⟩
  · rfl
  · right
    simp [record, reportedWriteLedger, contract, writeLedger,
      initial, zeroNormalAccounting, Ledger.obeysCaps, Ledger.totalCalls]

theorem writtenState_history (E : BinaryExperiment) (truth : single.Stage → Bool) :
    (writtenState E truth).history = [.wrote head false 0, .report head (truth head) 0] := by
  simp [writtenState, record, writeResponses, contract, initial, writeLedger]

theorem prefix_cases (E : BinaryExperiment) (truth : single.Stage → Bool)
    (tapes : ReviewTapes (input E)) {n : ℕ} {state : State single}
    (hp : Prefix (input E) contract .native (zeroNormalAccounting single) rule () truth tapes n state) :
    state = initial truth ∨ state = writtenState E truth ∨ state.halted = true := by
  induction hp with
  | initial => exact Or.inl rfl
  | @next n before after earlier step ih =>
    rcases ih with hi | hw | hh
    · subst before
      have he := step_deterministic (input E) contract .native (zeroNormalAccounting single)
        tapes step (write_step E truth tapes)
      exact Or.inr (Or.inl he)
    · subst before
      have ha : (writtenState E truth).halted = false := rfl
      have hrl : rule () (writtenState E truth).history = .stop := by
        simp [rule, writtenState_history]
      rw [hrl] at step
      have he := step_deterministic (input E) contract .native (zeroNormalAccounting single)
        tapes step (Step.stop (writtenState E truth) ha)
      exact Or.inr (Or.inr (he ▸ rfl))
    · have ha := step_source_active (input E) contract .native (zeroNormalAccounting single) tapes step
      simp [hh] at ha

theorem rule_legal (E : BinaryExperiment) :
    LegalRule (input E) contract .native (zeroNormalAccounting single) rule := by
  intro seed truth tapes n state hp ha
  cases seed
  rcases prefix_cases E truth tapes hp with hi | hw | hh
  · subst state
    exact ⟨writtenState E truth, write_step E truth tapes⟩
  · subst state
    refine ⟨stopState (writtenState E truth) false, ?_⟩
    simpa [rule, writtenState_history] using Step.stop (input := input E) (C := contract)
      (mode := .native) (accounting := zeroNormalAccounting single)
      (tapes := tapes) (writtenState E truth) ha
  · simp [hh] at ha

noncomputable def policy (E : BinaryExperiment) :
    Policy (input E) contract .native (zeroNormalAccounting single) Unit where
  rule := rule
  measurable_rule := measurable_of_countable _
  legal := rule_legal E


theorem stage_eq_head (stage : single.Stage) : stage = head := by
  apply Fin.ext
  have h := stage.isLt
  change stage.val < 1 at h
  change stage.val = 0
  omega

theorem truth_eq_false_of_head (truth : single.Stage → Bool) (h : truth head = false) :
    truth = fun _ => false := by
  funext stage
  simpa only [stage_eq_head stage] using h

theorem run_one (E : BinaryExperiment) (sample : Unit × (input E).World) :
    run (input E) contract .native (zeroNormalAccounting single) rule sample 1 =
      writtenState E ((input E).truthAt sample.2) := by
  apply run_succ_of_step
  · rfl
  · exact write_step E _ _

theorem run_two (E : BinaryExperiment) (sample : Unit × (input E).World) :
    run (input E) contract .native (zeroNormalAccounting single) rule sample 2 =
      stopState (writtenState E ((input E).truthAt sample.2)) false := by
  apply run_succ_of_step
  · rw [run_one]
    rfl
  · rw [run_one]
    have ha : (writtenState E ((input E).truthAt sample.2)).halted = false := rfl
    simpa [rule, writtenState_history] using Step.stop (input := input E) (C := contract)
      (mode := .native) (accounting := zeroNormalAccounting single)
      (tapes := worldTapes (input E) sample.2) (writtenState E ((input E).truthAt sample.2)) ha

theorem success_of_truth_false (E : BinaryExperiment) (sample : Unit × (input E).World)
    (htruth : (input E).truthAt sample.2 head = false) :
    runSuccess (input E) contract .native (zeroNormalAccounting single) rule sample := by
  refine ⟨2, ?_, ?_⟩
  · rw [run_two]
    rfl
  · rw [run_two]
    have ht := truth_eq_false_of_head _ htruth
    rw [ht]
    simp [writtenState, stopState, record, reportedWriteLedger, contract, writeLedger,
      initial, zeroNormalAccounting, Ledger.success, Ledger.windowObligations,
      allWritten, stage_eq_head]

theorem run_reviews_zero (E : BinaryExperiment) (sample : Unit × (input E).World)
    (n : ℕ) (stage : single.Stage) :
    (run (input E) contract .native (zeroNormalAccounting single) rule sample n).ledger.reviews stage = 0 := by
  rcases n with _ | n
  · rfl
  rcases n with _ | n
  · rw [show 0 + 1 = 1 from rfl, run_one]
    simp [writtenState, record, reportedWriteLedger, contract, writeLedger, initial]
  · have hh : (run (input E) contract .native (zeroNormalAccounting single) rule sample 2).halted = true := by
      rw [run_two]
      rfl
    have he := run_after_halt (input E) contract .native (zeroNormalAccounting single) rule sample 2 hh n
    rw [show n + 1 + 1 = 2 + n by omega, he, run_two]
    simp [writtenState, stopState, record, reportedWriteLedger, contract, writeLedger, initial]

theorem futureObservationBill_zero (E : BinaryExperiment) (sample : Unit × (input E).World) :
    futureObservationBill (input E) contract .native (zeroNormalAccounting single) rule 1 sample = 0 := by
  simp [futureObservationBill, observationIncrement, run_reviews_zero]

noncomputable def startup (E : BinaryExperiment) : Startup single :=
  publicStartup (writtenState E (fun _ => false))

theorem historyGate_eq_truth (E : BinaryExperiment) :
    historyGate (input E) contract .native (zeroNormalAccounting single) rule 1 (startup E) Set.univ =
      {sample : Unit × (input E).World | (input E).truthAt sample.2 head = false} := by
  ext sample
  simp only [historyGate, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ,
    and_true, run_one, startup]
  constructor
  · intro hh
    have hhist := congrArg Startup.history hh
    simp only [publicStartup, writtenState_history] at hhist
    have hreports := List.cons.inj hhist |>.2
    have hevents := List.cons.inj hreports |>.1
    exact congrArg (fun event : VisibleEvent single => match event with
      | .report _ truth _ => truth
      | _ => true) hevents
  · intro ht
    rw [truth_eq_false_of_head _ ht]

theorem historyGate_positive (E : BinaryExperiment) :
    0 < (input E).seededWorldLaw (Measure.dirac ())
      (historyGate (input E) contract .native (zeroNormalAccounting single) rule 1 (startup E) Set.univ) := by
  rw [historyGate_eq_truth]
  have he : {sample : Unit × (input E).World | (input E).truthAt sample.2 head = false} =
      Set.univ ×ˢ {world | (input E).truthAt world head = false} := by
    ext sample
    simp
  rw [StatisticalInput.seededWorldLaw, he, Measure.prod_prod]
  simpa only [measure_univ, one_mul] using (input E).worldLaw_truth_pos head false

theorem gate_healthy (E : BinaryExperiment) :
    ∀ sample ∈ historyGate (input E) contract .native (zeroNormalAccounting single) rule 1 (startup E) Set.univ,
      (run (input E) contract .native (zeroNormalAccounting single) rule sample 1).cursor = 0 ∧
      DeadlineViableBefore contract (run (input E) contract .native (zeroNormalAccounting single) rule sample 1) 0 := by
  intro sample _
  constructor
  · rw [run_one]
    rfl
  · constructor
    · rw [run_one]
      refine ⟨rfl, rfl, ?_⟩
      intro stage hs
      omega
    · intro hcurrent
      cases hcurrent

theorem comparisonCharge_zero_on_gate (E : BinaryExperiment) (price : ℝ≥0∞)
    (sample : Unit × (input E).World)
    (hs : sample ∈ historyGate (input E) contract .native (zeroNormalAccounting single) rule 1 (startup E) Set.univ) :
    historyComparisonCharge (input E) contract .native (zeroNormalAccounting single) rule 1 price sample = 0 := by
  have ht : (input E).truthAt sample.2 head = false := by
    rwa [historyGate_eq_truth] at hs
  simp [historyComparisonCharge, futureObservationBill_zero, success_of_truth_false E sample ht]

theorem not_allHealthyHistoryPenaltyBridge (E : BinaryExperiment) :
    ¬ AllHealthyHistoryPenaltyBridge.{0} (input E) := by
  intro hbridge
  obtain ⟨price, hp, hg⟩ := exists_positive_freshPenalty E
  have h := hbridge contract ⟨rfl,rfl⟩ (zeroNormalAccounting single) Unit inferInstance
    (policy E) (Measure.dirac ()) inferInstance 0 1 (by decide) (startup E) Set.univ
    MeasurableSet.univ (gate_healthy E) (ENNReal.ofReal price)
  dsimp only [policy] at h
  have htools : (startup E).availableTools = ∅ := by
    let : IsEmpty single.Tool := inferInstanceAs (IsEmpty (Fin 0))
    exact Finset.eq_empty_of_isEmpty _
  have hz : (∫⁻ sample in historyGate (input E) contract .native (zeroNormalAccounting single) rule
      1 (startup E) Set.univ,
      historyComparisonCharge (input E) contract .native (zeroNormalAccounting single) rule
        1 (ENNReal.ofReal price) sample ∂(input E).seededWorldLaw (Measure.dirac ())) = 0 := by
    apply setLIntegral_eq_zero
    · exact measurableSet_historyGate (input E) contract .native (zeroNormalAccounting single)
        rule (measurable_of_countable _) 1 (startup E) Set.univ MeasurableSet.univ
    intro sample hs
    exact comparisonCharge_zero_on_gate E _ sample hs
  change (input E).healthyPenalty 0 (startup E).availableTools (ENNReal.ofReal price) * _ ≤ _ at h
  rw [htools, hz] at h
  exact (not_le_of_gt (ENNReal.mul_pos hg.ne' (historyGate_positive E).ne')) h


/-- An explicit finite rational informative experiment, so the negative
result above has a closed witness rather than an experiment hypothesis. -/
def experiment : BinaryExperiment where
  alphabetSize := 2
  priorOne := 1 / 2
  prior_pos := by norm_num
  prior_lt_one := by norm_num
  channel := fun truth symbol => if truth = decide (symbol.val = 1) then 3 / 4 else 1 / 4
  channel_pos := by intro truth symbol; split <;> norm_num
  channel_sum := by intro truth; cases truth <;> norm_num [Fin.sum_univ_two]
  channel_distinct := by
    intro heq
    have hz := congrFun heq (0 : Fin 2)
    norm_num at hz
  observationFee := 1
  observationFee_pos := by norm_num

theorem concrete_counterexample :
    ¬ AllHealthyHistoryPenaltyBridge.{0} (input experiment) :=
  not_allHealthyHistoryPenaltyBridge experiment

/-- The obstructing public record is intentionally beyond first entry;
no theorem of the already-proved first-entry scope is contradicted. -/
theorem not_firstEntry (E : BinaryExperiment) (sample : Unit × (input E).World) :
    ¬ FirstEntryAt (input E) contract .native (zeroNormalAccounting single) rule 0 1 sample := by
  intro h
  exact h.2 0 (by decide) rfl

end PaperProofs.Common.Native.B09Counterexample
