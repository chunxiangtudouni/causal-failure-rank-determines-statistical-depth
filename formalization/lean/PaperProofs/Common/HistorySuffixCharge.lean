module

public import PaperProofs.Common.HistorySuffixFullRun
public import PaperProofs.Common.ReferenceSuffixRun
import Lean.Elab.Tactic.Omega

/-! Pathwise charges of the concrete B09 replay controller, preserving all
failed-path observations and infinite observation suprema. -/

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance} {Seed : Type*}

private theorem reportedWrite_reviews_same (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

/-- Reviews cannot revisit a stage strictly behind the actual cursor. -/
theorem run_reviews_behind_cursor (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (start extra : ℕ) (stage : I.Stage)
    (hold : stage.val < (run input C mode accounting rule sample start).cursor) :
    (run input C mode accounting rule sample (start + extra)).ledger.reviews stage =
      (run input C mode accounting rule sample start).ledger.reviews stage := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    by_cases hh : (run input C mode accounting rule sample (start + extra)).halted = true
    · rw [Nat.add_succ, run_succ_of_halted input C mode accounting rule sample (start + extra) hh]
      exact ih
    · have ha : (run input C mode accounting rule sample (start + extra)).halted = false := Bool.eq_false_iff.mpr hh
      obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample (start + extra)
      obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
      rw [Nat.add_succ, run_succ_of_step input C mode accounting rule sample (start + extra) next ha hs]
      have hc := run_cursor_monotone input C mode accounting rule hlegal sample (Nat.le_add_right start extra)
      change (run input C mode accounting rule sample start).cursor ≤
        (run input C mode accounting rule sample (start + extra)).cursor at hc
      generalize rule sample.1 (run input C mode accounting rule sample (start + extra)).history = action at hs
      cases hs with
      | review current live port resources =>
        have hne : stage ≠ current := by intro he; have hl := live.2; subst current; omega
        simpa only [record, reviewLedger, Function.update_of_ne hne] using ih
      | write current bit live port resources => simpa only [record, reportedWrite_reviews_same] using ih
      | allocate | execute | advance | stop | abandon => exact ih

theorem firstEntry_observationIncrement_eq_future_sum (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first start now : ℕ) (hentry : FirstEntryAt input C mode accounting rule first start sample)
    (hnow : start ≤ now) :
    observationIncrement input (run input C mode accounting rule sample start) (run input C mode accounting rule sample now) =
      ∑ stage : (I.freshSuffix first).Stage,
        ENNReal.ofReal (input.fees.observation (I.freshStageLift first stage) : ℝ) *
          ((run input C mode accounting rule sample now).ledger.reviews (I.freshStageLift first stage) : ℝ≥0∞) := by
  rw [← sum_referenceSuffix_stages I first (fun stage =>
    ENNReal.ofReal (input.fees.observation stage : ℝ) * ((run input C mode accounting rule sample now).ledger.reviews stage : ℝ≥0∞))]
  unfold observationIncrement
  apply Finset.sum_congr rfl
  intro stage _
  by_cases hf : first ≤ stage.val
  · have hz := (firstEntryAt_unborn input C mode accounting rule hlegal sample first start hentry).2 stage hf |>.2
    simp only [hf, ↓reduceIte, hz, tsub_zero]
  · have hold : stage.val < (run input C mode accounting rule sample start).cursor := by rw [hentry.1]; omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hnow
    rw [run_reviews_behind_cursor input C mode accounting rule hlegal sample start extra stage hold]
    simp only [hf, ↓reduceIte, tsub_self, ENat.toENNReal_zero, mul_zero]

/-- At every fresh-system clock its exact paid observation bill equals the
original remaining observation increment at the true replay clock. -/
theorem replayedSuffix_prefix_observationBill (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C mode accounting rule first start sample) (k : ℕ) :
    let startup := publicStartup (run input C mode accounting rule sample start)
    let targetRule := guardedReplayRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    (run (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) k).ledger.observationBill
        (input.freshSuffix first).fees =
      observationIncrement input (run input C mode accounting rule sample start)
        (run input C mode accounting rule sample (replaySourceClock input C mode accounting rule sample first start k)) := by
  have hv := (replayedSuffix_fullRun input C hearly hcurrent mode accounting rule hlegal sample first start hentry k).1
  rw [firstEntry_observationIncrement_eq_future_sum input C mode accounting rule hlegal sample first start _ hentry
    (replaySourceClock_ge_start input C mode accounting rule sample first start k)]
  unfold Ledger.observationBill
  apply Finset.sum_congr rfl
  intro stage _
  have hf : first ≤ (I.freshStageLift first stage).val := by change first ≤ first + stage.val; omega
  have hh := hv.reviews (I.freshStageLift first stage) hf
  rw [suffixStageOf_freshStageLift] at hh
  have hfee : (input.freshSuffix first).fees.observation stage = input.fees.observation (I.freshStageLift first stage) :=
    congrArg BinaryExperiment.observationFee (input.freshSuffix_experiment first stage)
  rw [hfee, hh]

/-- The analysis clock grows by at least one while the source stays active.
If it stops growing, the genuine original interpreter has already halted. -/
theorem replaySourceClock_grows_or_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (first start k : ℕ) :
    start + k ≤ replaySourceClock input C mode accounting rule sample first start k ∨
      (run input C mode accounting rule sample (replaySourceClock input C mode accounting rule sample first start k)).halted = true := by
  induction k with
  | zero => exact .inl le_rfl
  | succ k ih =>
    simp only [replaySourceClock]
    split
    next hh => exact .inr hh
    next hh =>
      have hbound : start + k ≤ replaySourceClock input C mode accounting rule sample first start k :=
        ih.resolve_right hh
      exact .inl (by omega)

/-- Exact remaining observation charge, including infinity and observations
on paths which later fail. Supremum cofinality follows from growth while
active and from unchanged genuine source state after halt. -/
theorem replayedSuffix_observationBill_eq (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C mode accounting rule first start sample) :
    let startup := publicStartup (run input C mode accounting rule sample start)
    let targetRule := guardedReplayRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    runObservationBill (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) =
      futureObservationBill input C mode accounting rule start sample := by
  let startup := publicStartup (run input C mode accounting rule sample start)
  let targetRule := guardedReplayRule (I := I.freshSuffix first) startup.availableTools
    (replayedSuffixCandidate first accounting rule startup)
  let targetAt := fun k => run (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) k
  let clock := replaySourceClock input C mode accounting rule sample first start
  let g := fun n => observationIncrement input (run input C mode accounting rule sample start)
    (run input C mode accounting rule sample n)
  have hmono : Monotone g := by
    intro a b hab
    apply Finset.sum_le_sum
    intro stage _
    exact mul_le_mul_right (ENat.toENNReal_mono
      (tsub_le_tsub_right (run_reviews_mono input C mode accounting rule hlegal sample stage hab) _)) _
  have hprefix (k : ℕ) : (targetAt k).ledger.observationBill (input.freshSuffix first).fees = g (clock k) :=
    replayedSuffix_prefix_observationBill input C hearly hcurrent mode accounting rule hlegal sample first start hentry k
  change (⨆ k, (targetAt k).ledger.observationBill (input.freshSuffix first).fees) = ⨆ extra, g (start + extra)
  apply le_antisymm
  · apply iSup_le
    intro k
    rw [hprefix]
    obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le (replaySourceClock_ge_start input C mode accounting rule sample first start k)
    change clock k = start + extra at he
    rw [he]
    exact le_iSup (fun extra => g (start + extra)) extra
  · apply iSup_le
    intro extra
    have hcofinal : g (start + extra) ≤ g (clock extra) := by
      rcases replaySourceClock_grows_or_halted input C mode accounting rule sample first start extra with hbound | hhalt
      · exact hmono hbound
      · by_cases hle : start + extra ≤ clock extra
        · exact hmono hle
        · obtain ⟨delta, he⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge hle)
          change start + extra = clock extra + delta at he
          change observationIncrement input _ _ ≤ observationIncrement input _ _
          rw [he, run_after_halt input C mode accounting rule sample (clock extra) hhalt delta]
    exact hcofinal.trans ((hprefix extra).symm.le.trans (le_iSup (fun k => (targetAt k).ledger.observationBill (input.freshSuffix first).fees) extra))

end PaperProofs.Common.Native
