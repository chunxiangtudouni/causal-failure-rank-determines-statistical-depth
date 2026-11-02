module

public import PaperProofs.Paid.PDMenu_SuffixActualCharge_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

theorem observationBill_suffixRun_view {Seed : Type*}
    (input : StatisticalInput I) (first : ℕ) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (childC : Contract (I.freshSuffix first))
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (hchildLegal : LegalRule (input.freshSuffix first) childC .uncapped childAccounting childRule)
    (sample : Seed × input.World) (before : List (VisibleEvent I)) (start : ℕ)
    (hbefore : ∀ stage : (I.freshSuffix first).Stage,
      historyObservations before (I.freshStageLift first stage) = [])
    (views : ∀ k : ℕ, ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k)) :
    ∀ k : ℕ,
    (run input C .uncapped accounting rule sample (start + k)).ledger.observationBill input.fees =
      (run input C .uncapped accounting rule sample start).ledger.observationBill input.fees +
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k).ledger.observationBill (input.freshSuffix first).fees := by
  let childSample := (sample.1, referenceSuffixWorld input first sample.2)
  let parentAt := fun k => run input C .uncapped accounting rule sample (start + k)
  let childAt := fun k => run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k
  have hcounts (k : ℕ) (stage : (I.freshSuffix first).Stage) :
      (parentAt k).ledger.reviews (I.freshStageLift first stage) = (childAt k).ledger.reviews stage := by
    obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (start + k)
    obtain ⟨n, _, hc⟩ := run_has_prefix (input.freshSuffix first) childC .uncapped childAccounting childRule hchildLegal childSample k
    exact referenceSuffix_reviews_of_prefixes input first C accounting rule childC childAccounting childRule
      sample.1 _ _ _ _ hp hc before (views k) hbefore stage
  have hcursor : (run input C .uncapped accounting rule sample start).cursor = first := by
    simpa only [Nat.add_zero, run, initial] using (views 0).cursor
  intro k
  rw [observationBill_eq_prefix_add_increment input _ _
    (fun stage => run_reviews_mono input C .uncapped accounting rule hlegal sample stage (Nat.le_add_right start k))]
  apply congrArg ((run input C .uncapped accounting rule sample start).ledger.observationBill input.fees + ·)
  change observationIncrement input (run input C .uncapped accounting rule sample start) (parentAt k) =
    (childAt k).ledger.observationBill (input.freshSuffix first).fees
  have hsum : observationIncrement input (run input C .uncapped accounting rule sample start) (parentAt k) =
      ∑ stage : I.Stage, if first ≤ stage.val then
        ENNReal.ofReal (input.fees.observation stage : ℝ) * ((parentAt k).ledger.reviews stage : ℝ≥0∞) else 0 := by
    unfold observationIncrement
    apply Finset.sum_congr rfl
    intro stage _
    by_cases hf : first ≤ stage.val
    · let target := suffixStageOf first stage hf
      have hlift : I.freshStageLift first target = stage := freshStageLift_suffixStageOf first stage hf
      have hz := hcounts 0 target
      change (run input C .uncapped accounting rule sample (start + 0)).ledger.reviews
        (I.freshStageLift first target) = 0 at hz
      rw [Nat.add_zero, hlift] at hz
      simp only [hf, ↓reduceIte, hz, tsub_zero]
    · have hold : stage.val < (run input C .uncapped accounting rule sample start).cursor := by rw [hcursor]; omega
      have he := run_reviews_behind_cursor input C .uncapped accounting rule hlegal sample start k stage hold
      change (parentAt k).ledger.reviews stage = _ at he
      simp only [hf, ↓reduceIte, he, tsub_self, ENat.toENNReal_zero, mul_zero]
  rw [hsum, sum_referenceSuffix_stages]
  unfold Ledger.observationBill
  apply Finset.sum_congr rfl
  intro stage _
  have hfee := congrArg PaperProofs.Statistics.BinaryExperiment.observationFee
    (input.freshSuffix_experiment first stage)
  change (input.freshSuffix first).fees.observation stage = input.fees.observation (I.freshStageLift first stage) at hfee
  rw [hfee, hcounts k stage]


/-- Exact full ACTUAL bill decomposition, including all executed correction
fees on every finite, infinite, failed and abandoned continuation path. -/
theorem runActualBill_suffixRun_view {Seed : Type*}
    (input : StatisticalInput I) (first : ℕ) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (childC : Contract (I.freshSuffix first))
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (hchildLegal : LegalRule (input.freshSuffix first) childC .uncapped childAccounting childRule)
    (sample : Seed × input.World) (before : List (VisibleEvent I)) (start : ℕ)
    (hbefore : ∀ stage : (I.freshSuffix first).Stage,
      historyObservations before (I.freshStageLift first stage) = [])
    (views : ∀ k : ℕ, ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k)) :
    runActualBill input C .uncapped accounting rule sample =
      ((run input C .uncapped accounting rule sample start).ledger.observationBill input.fees +
        historyCorrectionCharge input before) +
      runActualBill (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) := by
  have hpoint (k : ℕ) :
      (run input C .uncapped accounting rule sample (start + k)).ledger.actualBill input.fees =
        ((run input C .uncapped accounting rule sample start).ledger.observationBill input.fees +
          historyCorrectionCharge input before) +
        (run (input.freshSuffix first) childC .uncapped childAccounting childRule
          (sample.1, referenceSuffixWorld input first sample.2) k).ledger.actualBill (input.freshSuffix first).fees := by
    obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (start + k)
    obtain ⟨_, _, hc⟩ := run_has_prefix (input.freshSuffix first) childC .uncapped childAccounting childRule
      hchildLegal (sample.1, referenceSuffixWorld input first sample.2) k
    have hcorr := correctionBill_suffixView input first C accounting rule childC childAccounting childRule
      sample.1 _ _ _ _ hp hc before (views k)
    unfold Ledger.actualBill
    rw [observationBill_suffixRun_view input first C accounting rule hlegal childC childAccounting
      childRule hchildLegal sample before start hbefore views k, hcorr]
    ac_rfl
  unfold runActualBill
  rw [← (run_bill_mono input C .uncapped accounting rule sample).iSup_nat_add start, ENNReal.add_iSup]
  apply iSup_congr
  intro k
  rw [Nat.add_comm k start]
  exact hpoint k

/-- A successful actual child transfers success to the original task, and
full actual fees split exactly. Thus the paid charge is bounded without
conditioning away failed-path corrections or supposing finite expected cost. -/
theorem runPaidPenaltyCharge_suffixRun_le {Seed : Type*}
    (input : StatisticalInput I) (first : ℕ) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (childC : Contract (I.freshSuffix first))
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (hchildLegal : LegalRule (input.freshSuffix first) childC .uncapped childAccounting childRule)
    (sample : Seed × input.World) (before : List (VisibleEvent I)) (start : ℕ)
    (hbefore : ∀ stage : (I.freshSuffix first).Stage,
      historyObservations before (I.freshStageLift first stage) = [])
    (views : ∀ k : ℕ, ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k))
    (hearly : C.reporting = .early)
    (hbeforeWrite : ∀ stage : (I.freshSuffix first).Stage,
      historyWrite before (I.freshStageLift first stage) = none)
    (hresolved : ∀ stage : I.Stage, stage.val < first →
      historyWritten before stage = some (input.truthAt sample.2 stage) ∨
        ∃ pair ∈ historyExecutions before, pair.1.stage = stage)
    (penalty : ℝ≥0∞) :
    runPaidPenaltyCharge input C accounting rule penalty sample ≤
      ((run input C .uncapped accounting rule sample start).ledger.observationBill input.fees +
        historyCorrectionCharge input before) +
      runPaidPenaltyCharge (input.freshSuffix first) childC childAccounting childRule penalty
        (sample.1, referenceSuffixWorld input first sample.2) := by
  classical
  unfold runPaidPenaltyCharge
  rw [runActualBill_suffixRun_view input first C accounting rule hlegal childC childAccounting
    childRule hchildLegal sample before start hbefore views, add_assoc]
  apply add_le_add le_rfl
  apply add_le_add le_rfl
  by_cases hs : runSuccess (input.freshSuffix first) childC .uncapped childAccounting childRule
      (sample.1, referenceSuffixWorld input first sample.2)
  · have hp := suffixRun_success_of_views input first C hearly accounting rule hlegal childC
      childAccounting childRule hchildLegal sample before start hbeforeWrite hresolved views hs
    simp only [hs, hp, ite_true, le_refl]
  · rw [ite_eq_right hs]
    split_ifs <;> simp

end PDMenu
