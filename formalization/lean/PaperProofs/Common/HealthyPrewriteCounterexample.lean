module

public import PaperProofs.Common.HealthyHistoryCounterexample
public import PaperProofs.Common.NativeBellmanUpper
public import PaperProofs.Statistics.StoppedInformation

/-! A pre-write native counterexample. Reviews already bought on
the CURRENT stage change its posterior; all comparisons use the original
fresh value and actual future observation increments. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace PaperProofs.Common.Native.B09PrewriteCounterexample

open PaperProofs.Statistics B09Counterexample

abbrev E := B09Counterexample.experiment
abbrev data := B09Counterexample.input E

def contract (n : ℕ) : Contract single :=
  ⟨.early, .currentWindow, .terminalBarrier, fun _ => n, n, 0⟩

def rule (n : ℕ) : PolicyRule single Unit := fun _ history =>
  if historyWritten history head = none then
    if (historyObservations history head).length < n then .review head else .write head false
  else .stop

def reviewState (truth : single.Stage → Bool) (tape : (data.experiment head).Tape) (m : ℕ) : State single :=
  { initial truth with
    ledger := {(initial truth).ledger with reviews := fun _ => m}
    clock := m
    history := headReviewHistory data head tape m }

theorem reviewState_zero (truth : single.Stage → Bool) (tape : (data.experiment head).Tape) :
    reviewState truth tape 0 = initial truth := rfl

theorem reviewState_history (truth : single.Stage → Bool) (tape : (data.experiment head).Tape) (m : ℕ) :
    (reviewState truth tape m).history = headReviewHistory data head tape m := rfl

theorem reviewState_historyWritten (truth : single.Stage → Bool) (tape : (data.experiment head).Tape) (m : ℕ) :
    historyWritten (reviewState truth tape m).history head = none :=
  historyWritten_headReviewHistory data head tape m

theorem reviewState_observations_length (truth : single.Stage → Bool) (tape : (data.experiment head).Tape) (m : ℕ) :
    (historyObservations (reviewState truth tape m).history head).length = m := by
  rw [reviewState_history, historyObservations_headReviewHistory]
  exact List.length_ofFn

theorem reviewState_caps (n m : ℕ) (hm : m ≤ n) (truth : single.Stage → Bool) (tape : (data.experiment head).Tape) :
    (reviewState truth tape m).ledger.obeysCaps (contract n) := by
  constructor
  · intro stage
    change (m : ℕ∞) ≤ (n : ℕ∞)
    exact_mod_cast hm
  · simp only [Ledger.totalCalls, reviewState, initial, contract]
    change (0 : ℕ∞) + (∑ _stage : single.Stage, (m : ℕ∞)) + 0 ≤ (n : ℕ∞)
    have hc : Fintype.card single.Stage = 1 := by decide
    simpa only [Finset.sum_const, Finset.card_univ, hc, one_nsmul, zero_add, add_zero] using
      (show (m : ℕ∞) ≤ (n : ℕ∞) by exact_mod_cast hm)

theorem reviewState_step (n m : ℕ) (hm : m < n) (truth : single.Stage → Bool)
    (tapes : ReviewTapes data) :
    Step data (contract n) .native (zeroNormalAccounting single) tapes
      (reviewState truth (tapes head) m) (.review head)
      (reviewState truth (tapes head) (m + 1)) := by
  have he : record (zeroNormalAccounting single) (reviewState truth (tapes head) m)
      (.review head) [.observation head (tapes head m).val]
      (reviewLedger (reviewState truth (tapes head) m) head) 0 false =
      reviewState truth (tapes head) (m + 1) := by
    have hf : Function.update (fun _ : single.Stage => (m : ℕ∞)) head ((m : ℕ∞) + 1) =
        (fun _ => (m : ℕ∞) + 1) := by
      funext stage
      rw [stage_eq_head stage, Function.update_self]
    simp only [record, reviewState, reviewLedger, zeroNormalAccounting, Nat.cast_zero, add_zero,
      Nat.cast_add, Nat.cast_one, headReviewHistory_succ, hf]
    rfl
  have hs := Step.review (input := data) (C := contract n) (mode := .native)
    (accounting := zeroNormalAccounting single) (tapes := tapes)
    (reviewState truth (tapes head) m) head ⟨rfl, rfl⟩ rfl
    (Or.inr (by
      change (record (zeroNormalAccounting single) (reviewState truth (tapes head) m)
        (.review head) [.observation head (tapes head m).val]
        (reviewLedger (reviewState truth (tapes head) m) head) 0 false).ledger.obeysCaps (contract n)
      rw [he]
      exact reviewState_caps n (m+1) (by omega) truth (tapes head)))
  change Step data (contract n) .native (zeroNormalAccounting single) tapes _ _
    (record (zeroNormalAccounting single) (reviewState truth (tapes head) m) (.review head)
      [.observation head (tapes head m).val] (reviewLedger (reviewState truth (tapes head) m) head) 0 false) at hs
  exact he ▸ hs

noncomputable def writtenState (n : ℕ) (truth : single.Stage → Bool) (tape : (data.experiment head).Tape) : State single :=
  let before := reviewState truth tape n
  record (zeroNormalAccounting single) before (.write head false)
    (writeResponses (contract n) before head false)
    (reportedWriteLedger (contract n) before head false) 0 false

theorem write_step (n : ℕ) (truth : single.Stage → Bool) (tapes : ReviewTapes data) :
    Step data (contract n) .native (zeroNormalAccounting single) tapes
      (reviewState truth (tapes head) n) (.write head false) (writtenState n truth (tapes head)) := by
  apply Step.write
  · exact ⟨rfl, rfl⟩
  · rfl
  · right
    change (writtenState n truth (tapes head)).ledger.obeysCaps (contract n)
    simpa only [writtenState, record, reportedWriteLedger, contract, ite_true, writeLedger,
      zeroNormalAccounting, Nat.cast_zero, zero_add, add_zero, Ledger.obeysCaps, Ledger.totalCalls, reviewState, initial]
      using reviewState_caps n n le_rfl truth (tapes head)

theorem writtenState_history (n : ℕ) (truth : single.Stage → Bool) (tape : (data.experiment head).Tape) :
    (writtenState n truth tape).history = headReviewHistory data head tape n ++
      [.wrote head false n, .report head (truth head) n] := by
  simp [writtenState, record, writeResponses, contract, reviewState, initial, writeLedger]

theorem writtenState_historyWritten (n : ℕ) (truth : single.Stage → Bool) (tape : (data.experiment head).Tape) :
    historyWritten (writtenState n truth tape).history head = some false := by
  rw [writtenState_history]
  have hw : (headReviewHistory data head tape n).filterMap (eventWrite head) = [] := by
    simp [headReviewHistory, eventWrite]
  simp only [historyWritten, historyWrite, List.filterMap_append, hw]
  rfl

theorem prefix_cases (n : ℕ) (truth : single.Stage → Bool) (tapes : ReviewTapes data)
    {k : ℕ} {state : State single}
    (hp : Prefix data (contract n) .native (zeroNormalAccounting single) (rule n) () truth tapes k state) :
    (∃ m ≤ n, state = reviewState truth (tapes head) m) ∨
      state = writtenState n truth (tapes head) ∨ state.halted = true := by
  induction hp with
  | initial => exact Or.inl ⟨0, Nat.zero_le _, rfl⟩
  | @next k before after earlier step ih =>
    rcases ih with ⟨m, hm, he⟩ | hw | hh
    · subst before
      have hraw : rule n () (reviewState truth (tapes head) m).history =
          if m < n then .review head else .write head false := by
        simp only [rule, reviewState_historyWritten, ite_true, reviewState_observations_length]
      rw [hraw] at step
      by_cases hlt : m < n
      · rw [ite_eq_left hlt] at step
        have he := step_deterministic data (contract n) .native (zeroNormalAccounting single)
          tapes step (reviewState_step n m hlt truth tapes)
        exact Or.inl ⟨m+1, by omega, he⟩
      · rw [ite_eq_right hlt] at step
        have heq : m = n := by omega
        subst m
        have he := step_deterministic data (contract n) .native (zeroNormalAccounting single)
          tapes step (write_step n truth tapes)
        exact Or.inr (Or.inl he)
    · subst before
      have hr : rule n () (writtenState n truth (tapes head)).history = .stop := by
        simp only [rule, writtenState_historyWritten, Option.some_ne_none, ite_false]
      rw [hr] at step
      have he := step_deterministic data (contract n) .native (zeroNormalAccounting single)
        tapes step (Step.stop (writtenState n truth (tapes head)) rfl)
      exact Or.inr (Or.inr (he ▸ rfl))
    · have ha := step_source_active data (contract n) .native (zeroNormalAccounting single) tapes step
      simp [hh] at ha

theorem rule_legal (n : ℕ) :
    LegalRule data (contract n) .native (zeroNormalAccounting single) (rule n) := by
  intro seed truth tapes k state hp ha
  cases seed
  rcases prefix_cases n truth tapes hp with ⟨m, hm, he⟩ | hw | hh
  · subst state
    simp only [rule, reviewState_historyWritten, ite_true, reviewState_observations_length]
    by_cases hlt : m < n
    · rw [ite_eq_left hlt]
      exact ⟨_, reviewState_step n m hlt truth tapes⟩
    · rw [ite_eq_right hlt]
      have heq : m = n := by omega
      subst m
      exact ⟨_, write_step n truth tapes⟩
  · subst state
    refine ⟨stopState (writtenState n truth (tapes head)) false, ?_⟩
    simpa only [rule, writtenState_historyWritten, Option.some_ne_none, ite_false] using
      Step.stop (input := data) (C := contract n) (mode := .native)
        (accounting := zeroNormalAccounting single) (tapes := tapes)
        (writtenState n truth (tapes head)) ha
  · simp [hh] at ha

noncomputable def policy (n : ℕ) : Policy data (contract n) .native (zeroNormalAccounting single) Unit where
  rule := rule n
  measurable_rule := measurable_of_countable _
  legal := rule_legal n

theorem run_before (n m : ℕ) (hm : m ≤ n) (sample : Unit × data.World) :
    run data (contract n) .native (zeroNormalAccounting single) (rule n) sample m =
      reviewState (data.truthAt sample.2) (worldTapes data sample.2 head) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hlt : m < n := by omega
    have hr := ih (by omega)
    apply run_succ_of_step data (contract n) .native (zeroNormalAccounting single) (rule n) sample m _
    · rw [hr]
      rfl
    · rw [hr]
      simp only [rule, reviewState_historyWritten, ite_true, reviewState_observations_length, hlt]
      exact reviewState_step n m hlt _ _

theorem run_write (n : ℕ) (sample : Unit × data.World) :
    run data (contract n) .native (zeroNormalAccounting single) (rule n) sample (n + 1) =
      writtenState n (data.truthAt sample.2) (worldTapes data sample.2 head) := by
  apply run_succ_of_step
  · rw [run_before n n le_rfl]
    rfl
  · rw [run_before n n le_rfl]
    simp only [rule, reviewState_historyWritten, ite_true, reviewState_observations_length, lt_self_iff_false, ite_false]
    exact write_step n _ _

theorem run_stop (n : ℕ) (sample : Unit × data.World) :
    run data (contract n) .native (zeroNormalAccounting single) (rule n) sample (n + 2) =
      stopState (writtenState n (data.truthAt sample.2) (worldTapes data sample.2 head)) false := by
  apply run_succ_of_step
  · rw [run_write]
    rfl
  · rw [run_write]
    simpa only [rule, writtenState_historyWritten, Option.some_ne_none, ite_false] using
      Step.stop (input := data) (C := contract n) (mode := .native)
        (accounting := zeroNormalAccounting single) (tapes := worldTapes data sample.2)
        (writtenState n (data.truthAt sample.2) (worldTapes data sample.2 head)) rfl

theorem success_of_truth_false (n : ℕ) (sample : Unit × data.World)
    (htruth : data.truthAt sample.2 head = false) :
    runSuccess data (contract n) .native (zeroNormalAccounting single) (rule n) sample := by
  refine ⟨n+2, ?_, ?_⟩
  · rw [run_stop]
    rfl
  · rw [run_stop]
    have ht := truth_eq_false_of_head _ htruth
    rw [ht]
    simp [writtenState, stopState, record, reportedWriteLedger, contract, writeLedger,
      reviewState, initial, zeroNormalAccounting, Ledger.success, Ledger.windowObligations,
      allWritten, stage_eq_head]

theorem run_reviews_after (n k : ℕ) (sample : Unit × data.World) (stage : single.Stage) :
    (run data (contract n) .native (zeroNormalAccounting single) (rule n) sample (n+k)).ledger.reviews stage = n := by
  rcases k with _ | k
  · rw [Nat.add_zero, run_before n n le_rfl]
    rfl
  rcases k with _ | k
  · rw [Nat.add_zero, run_write]
    rfl
  · have hh : (run data (contract n) .native (zeroNormalAccounting single) (rule n) sample (n+2)).halted = true := by
      rw [run_stop]
      rfl
    have he := run_after_halt data (contract n) .native (zeroNormalAccounting single) (rule n) sample (n+2) hh k
    rw [show n+(k+1+1) = (n+2)+k by omega, he, run_stop]
    rfl

theorem futureObservationBill_zero (n : ℕ) (sample : Unit × data.World) :
    futureObservationBill data (contract n) .native (zeroNormalAccounting single) (rule n) n sample = 0 := by
  simp [futureObservationBill, observationIncrement, run_reviews_after,
    run_before n n le_rfl, reviewState]

def zeroTape : (data.experiment head).Tape := fun _ => ⟨0, by decide⟩

noncomputable def startup (n : ℕ) : Startup single :=
  publicStartup (reviewState (fun _ => false) zeroTape n)

theorem historyGate_eq_prefix (n : ℕ) :
    historyGate data (contract n) .native (zeroNormalAccounting single) (rule n) n (startup n) Set.univ =
      {sample : Unit × data.World | ∀ k : Fin n, worldTapes data sample.2 head k.val = zeroTape k.val} := by
  ext sample
  simp only [historyGate, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ,
    and_true, run_before n n le_rfl, startup]
  constructor
  · intro hh k
    have hhist := congrArg Startup.history hh
    change headReviewHistory data head (worldTapes data sample.2 head) n =
      headReviewHistory data head zeroTape n at hhist
    have he := congrFun (List.ofFn_injective hhist) k
    exact Fin.ext (VisibleEvent.observation.inj he).2
  · intro ht
    have hh := headReviewHistory_prefix data head (worldTapes data sample.2 head) zeroTape n
      (fun k hk => ht ⟨k,hk⟩)
    simp only [publicStartup, reviewState, initial, hh]

theorem gate_unwritten_healthy (n : ℕ) (sample : Unit × data.World) :
    (run data (contract n) .native (zeroNormalAccounting single) (rule n) sample n).cursor = 0 ∧
    DeadlineViableBefore (contract n)
      (run data (contract n) .native (zeroNormalAccounting single) (rule n) sample n) 0 ∧
    (run data (contract n) .native (zeroNormalAccounting single) (rule n) sample n).ledger.written head = none ∧
    (run data (contract n) .native (zeroNormalAccounting single) (rule n) sample n).ledger.reportTime head = none := by
  rw [run_before n n le_rfl]
  refine ⟨rfl, ⟨?_, ?_⟩, rfl, rfl⟩
  · refine ⟨rfl, rfl, ?_⟩
    intro stage hs
    omega
  · intro hc
    cases hc

def word (n : ℕ) : (data.experiment head).StoppedWord := ⟨n, fun k => zeroTape k.val⟩

theorem wordProbability_false (n : ℕ) :
    (data.experiment head).wordProbability false (word n) = (3 / 4 : ℝ)^n := by
  change (∏ _k : Fin n, ((3 / 4 : ℚ) : ℝ)) = _
  norm_num [div_pow]

theorem wordProbability_true (n : ℕ) :
    (data.experiment head).wordProbability true (word n) = (1 / 4 : ℝ)^n := by
  change (∏ _k : Fin n, ((1 / 4 : ℚ) : ℝ)) = _
  norm_num [div_pow]

def prefixTruth (n : ℕ) (truth : Bool) : Set (Unit × data.World) :=
  {sample | data.truthAt sample.2 head = truth ∧
    ∀ k : Fin n, worldTapes data sample.2 head k.val = zeroTape k.val}

theorem prefixTruth_measure (n : ℕ) (truth : Bool) :
    data.seededWorldLaw (Measure.dirac ()) (prefixTruth n truth) =
      (data.experiment head).priorMass truth *
        ENNReal.ofReal ((data.experiment head).wordProbability truth (word n)) := by
  have he : prefixTruth n truth = Set.univ ×ˢ
      {world : data.World | world head ∈ ({truth} ×ˢ (data.experiment head).prefixEvent (word n))} := by
    ext sample
    simp [prefixTruth, StatisticalInput.truthAt, worldTapes,
      BinaryExperiment.prefixEvent, word, StatisticalInput.reviewAt]
  rw [he, StatisticalInput.seededWorldLaw, Measure.prod_prod, measure_univ, one_mul,
    data.worldLaw_truth_tape head truth _ ((data.experiment head).measurableSet_prefixEvent (word n)),
    (data.experiment head).tapeLaw_prefixEvent]

theorem prefixTruth_false_measure (n : ℕ) :
    data.seededWorldLaw (Measure.dirac ()) (prefixTruth n false) =
      ENNReal.ofReal ((1 / 2 : ℝ) * (3 / 4 : ℝ)^n) := by
  rw [prefixTruth_measure, wordProbability_false]
  have hp : (data.experiment head).priorMass false = ENNReal.ofReal (1 / 2 : ℝ) := by
    norm_num [BinaryExperiment.priorMass, BinaryExperiment.priorReal, BinaryExperiment.prior,
      data, B09Counterexample.input, E, B09Counterexample.experiment]
  rw [hp, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]

theorem prefixTruth_true_measure (n : ℕ) :
    data.seededWorldLaw (Measure.dirac ()) (prefixTruth n true) =
      ENNReal.ofReal ((1 / 2 : ℝ) * (1 / 4 : ℝ)^n) := by
  rw [prefixTruth_measure, wordProbability_true]
  have hp : (data.experiment head).priorMass true = ENNReal.ofReal (1 / 2 : ℝ) := by
    norm_num [BinaryExperiment.priorMass, BinaryExperiment.priorReal, BinaryExperiment.prior,
      data, B09Counterexample.input, E, B09Counterexample.experiment]
  rw [hp, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]

theorem historyGate_measure_lower (n : ℕ) :
    ENNReal.ofReal ((1 / 2 : ℝ) * (3 / 4 : ℝ)^n) ≤
      data.seededWorldLaw (Measure.dirac ())
        (historyGate data (contract n) .native (zeroNormalAccounting single) (rule n) n (startup n) Set.univ) := by
  rw [← prefixTruth_false_measure]
  apply measure_mono
  intro sample hs
  rw [historyGate_eq_prefix]
  exact hs.2

theorem historyGate_positive (n : ℕ) :
    0 < data.seededWorldLaw (Measure.dirac ())
      (historyGate data (contract n) .native (zeroNormalAccounting single) (rule n) n (startup n) Set.univ) :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) (pow_pos (by norm_num) n)))
    (historyGate_measure_lower n)

theorem comparisonCharge_le (n : ℕ) (price : ℝ≥0∞) (sample : Unit × data.World) :
    historyComparisonCharge data (contract n) .native (zeroNormalAccounting single) (rule n) n price sample ≤
      {sample : Unit × data.World | data.truthAt sample.2 head = true}.indicator (fun _ => price) sample := by
  by_cases ht : data.truthAt sample.2 head = true
  · rw [Set.indicator_of_mem (show sample ∈ {s : Unit × data.World | data.truthAt s.2 head = true} from ht)]
    simp only [historyComparisonCharge, futureObservationBill_zero, zero_add]
    split_ifs
    · exact bot_le
    · exact le_rfl
  · have hf : data.truthAt sample.2 head = false := Bool.eq_false_iff.mpr ht
    simp only [historyComparisonCharge, futureObservationBill_zero,
      success_of_truth_false n sample hf, ite_true, add_zero]
    exact bot_le

theorem comparison_integral_le (n : ℕ) (price : ℝ≥0∞) :
    (∫⁻ sample in historyGate data (contract n) .native (zeroNormalAccounting single) (rule n) n (startup n) Set.univ,
      historyComparisonCharge data (contract n) .native (zeroNormalAccounting single) (rule n) n price sample
        ∂data.seededWorldLaw (Measure.dirac ())) ≤
      price * ENNReal.ofReal ((1 / 2 : ℝ) * (1 / 4 : ℝ)^n) := by
  have hmeas : MeasurableSet {sample : Unit × data.World | data.truthAt sample.2 head = true} :=
    (measurableSet_singleton true).preimage ((data.measurable_truthAt head).comp measurable_snd)
  calc
    _ ≤ ∫⁻ sample in historyGate data (contract n) .native (zeroNormalAccounting single) (rule n) n (startup n) Set.univ,
        {sample : Unit × data.World | data.truthAt sample.2 head = true}.indicator (fun _ => price) sample
          ∂data.seededWorldLaw (Measure.dirac ()) := lintegral_mono (comparisonCharge_le n price)
    _ = price * data.seededWorldLaw (Measure.dirac ()) (prefixTruth n true) := by
      have he : {sample : Unit × data.World | data.truthAt sample.2 head = true} ∩
          historyGate data (contract n) .native (zeroNormalAccounting single) (rule n) n (startup n) Set.univ =
          prefixTruth n true := by
        ext sample
        rw [historyGate_eq_prefix]
        rfl
      rw [lintegral_indicator_const hmeas, Measure.restrict_apply hmeas, he]
    _ = _ := by rw [prefixTruth_true_measure]

theorem exists_strict_mass_violation :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ price : ℝ, 0 < price ∧
      ENNReal.ofReal price * ENNReal.ofReal ((1 / 2 : ℝ) * (1 / 4 : ℝ)^n) <
        data.healthyPenalty 0 ∅ (ENNReal.ofReal price) *
          ENNReal.ofReal ((1 / 2 : ℝ) * (3 / 4 : ℝ)^n) := by
  obtain ⟨price, hp, hG⟩ := exists_positive_freshPenalty E
  let G := data.healthyPenalty 0 ∅ (ENNReal.ofReal price)
  have hfinite : G ≠ ⊤ := data.healthyPenalty_ne_top 0 ∅ ENNReal.ofReal_ne_top
  let g : ℝ := G.toReal
  have hg : 0 < g := ENNReal.toReal_pos hG.ne' hfinite
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hg hp) (by norm_num : (1 / 3 : ℝ) < 1)
  let n := m + 1
  have hpow : (1 / 3 : ℝ)^n ≤ (1 / 3 : ℝ)^m := by
    dsimp only [n]
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1/3) m]
  have hratio : price * (1 / 3 : ℝ)^n < g := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow hp.le)
    simpa only [mul_comm] using (lt_div_iff₀ hp).mp hm
  let a : ℝ := (1 / 2 : ℝ) * (3 / 4 : ℝ)^n
  let b : ℝ := (1 / 2 : ℝ) * (1 / 4 : ℝ)^n
  have ha : 0 < a := mul_pos (by norm_num) (pow_pos (by norm_num) n)
  have hidentity : (1 / 3 : ℝ)^n * a = b := by
    dsimp only [a, b]
    calc
      _ = (1 / 2 : ℝ) * ((1 / 3 : ℝ)^n * (3 / 4 : ℝ)^n) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  have hreal : price * b < g * a := by
    calc
      _ = (price * (1 / 3 : ℝ)^n) * a := by rw [← hidentity]; ring
      _ < _ := mul_lt_mul_of_pos_right hratio ha
  have hENN := (ENNReal.ofReal_lt_ofReal_iff (mul_pos hg ha)).mpr hreal
  rw [ENNReal.ofReal_mul hp.le, ENNReal.ofReal_mul hg.le] at hENN
  have he : ENNReal.ofReal g = G := ENNReal.ofReal_toReal hfinite
  rw [he] at hENN
  exact ⟨n, by dsimp only [n]; omega, price, hp, hENN⟩

/-- A concrete native counterexample occurs after a positive number of
CURRENT reviews and strictly BEFORE the ordinary write or its report. The
gate is an actual positive-mass public history, not an analysis truth gate.
The original bridge inequality is strictly reversed on this gate. -/
theorem exists_prewrite_violation :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ price : ℝ, 0 < price ∧
      0 < data.seededWorldLaw (Measure.dirac ())
        (historyGate data (contract n) .native (zeroNormalAccounting single) (rule n) n (startup n) Set.univ) ∧
      (∀ sample ∈ historyGate data (contract n) .native (zeroNormalAccounting single) (rule n) n (startup n) Set.univ,
        (run data (contract n) .native (zeroNormalAccounting single) (rule n) sample n).cursor = 0 ∧
        DeadlineViableBefore (contract n)
          (run data (contract n) .native (zeroNormalAccounting single) (rule n) sample n) 0 ∧
        (run data (contract n) .native (zeroNormalAccounting single) (rule n) sample n).ledger.written head = none ∧
        (run data (contract n) .native (zeroNormalAccounting single) (rule n) sample n).ledger.reportTime head = none ∧
        (run data (contract n) .native (zeroNormalAccounting single) (rule n) sample n).ledger.reviews head = n) ∧
      (∀ sample : Unit × data.World,
        futureObservationBill data (contract n) .native (zeroNormalAccounting single) (rule n) n sample = 0) ∧
      (∫⁻ sample in historyGate data (contract n) .native (zeroNormalAccounting single) (rule n) n (startup n) Set.univ,
        historyComparisonCharge data (contract n) .native (zeroNormalAccounting single) (rule n) n
          (ENNReal.ofReal price) sample ∂data.seededWorldLaw (Measure.dirac ())) <
        data.healthyPenalty 0 (startup n).availableTools (ENNReal.ofReal price) *
          data.seededWorldLaw (Measure.dirac ())
            (historyGate data (contract n) .native (zeroNormalAccounting single) (rule n) n (startup n) Set.univ) := by
  obtain ⟨n, hn, price, hp, hmass⟩ := exists_strict_mass_violation
  refine ⟨n, hn, price, hp, historyGate_positive n, ?_, futureObservationBill_zero n, ?_⟩
  · intro sample _hs
    obtain ⟨hc, hh, hw, hr⟩ := gate_unwritten_healthy n sample
    refine ⟨hc, hh, hw, hr, ?_⟩
    rw [run_before n n le_rfl]
    rfl
  · have htools : (startup n).availableTools = ∅ := by
      let : IsEmpty single.Tool := inferInstanceAs (IsEmpty (Fin 0))
      exact Finset.eq_empty_of_isEmpty _
    rw [htools]
    calc
      _ ≤ ENNReal.ofReal price * ENNReal.ofReal ((1 / 2 : ℝ) * (1 / 4 : ℝ)^n) :=
        comparison_integral_le n (ENNReal.ofReal price)
      _ < data.healthyPenalty 0 ∅ (ENNReal.ofReal price) *
          ENNReal.ofReal ((1 / 2 : ℝ) * (3 / 4 : ℝ)^n) := hmass
      _ ≤ _ := mul_le_mul' le_rfl (historyGate_measure_lower n)

theorem not_allHealthyHistoryPenaltyBridge :
    ¬ AllHealthyHistoryPenaltyBridge.{0} data := by
  intro hbridge
  obtain ⟨n, _hn, price, _hp, _hpositive, hhealthy, _hfuture, hviol⟩ := exists_prewrite_violation
  have h := hbridge (contract n) ⟨rfl,rfl⟩ (zeroNormalAccounting single) Unit inferInstance
    (policy n) (Measure.dirac ()) inferInstance 0 n (by decide) (startup n) Set.univ MeasurableSet.univ
    (fun sample hs => ⟨(hhealthy sample hs).1, (hhealthy sample hs).2.1⟩) (ENNReal.ofReal price)
  exact (not_le_of_gt hviol) h

end PaperProofs.Common.Native.B09PrewriteCounterexample
