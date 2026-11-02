module

public import PaperProofs.Common.NativeSeed
public import PaperProofs.Common.NativeCostBound

/-!
Correction-price changes affect billing alone. The original contract, resource
mode, normal-call accounting, histories, observations, failures and private
randomness remain identical. This applies in native as well as uncapped mode;
it does not relax current execution/payment deadlines.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common

def StatisticalInput.withCorrectionFee {I : Instance} (input : StatisticalInput I)
    (fee : I.Stage → I.Tool → ℚ) (hfee : ∀ i r, 0 ≤ fee i r) : StatisticalInput I where
  experiment := input.experiment
  correctionFee := fee
  correctionFee_nonneg := hfee

namespace Native

variable {I : Instance} {Seed : Type*}

@[simp] theorem frozenTapes_reprice_eq (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (frontier : Frontier input) :
    frozenTapes (input.withCorrectionFee fee hfee) frontier = frozenTapes input frontier := rfl

@[simp] theorem frontierOf_reprice_eq (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (s : State I) (world : input.World) :
    frontierOf (input.withCorrectionFee fee hfee) s world = frontierOf input s world := rfl

theorem step_reprice_iff (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    (s next : State I) (action : Action I) :
    Step input C mode accounting tapes s action next ↔
      Step (input.withCorrectionFee fee hfee) C mode accounting tapes s action next := by
  constructor <;> intro h <;> cases h <;> constructor <;> assumption

theorem prefix_reprice_iff (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) (n : ℕ) (s : State I) :
    Prefix input C mode accounting policy seed truth tapes n s ↔
      Prefix (input.withCorrectionFee fee hfee) C mode accounting policy seed truth tapes n s := by
  constructor <;> intro hp
  · induction hp with
    | initial => exact .initial
    | next _ hs ih => exact .next ih ((step_reprice_iff input fee hfee C mode accounting tapes _ _ _).mp hs)
  · induction hp with
    | initial => exact .initial
    | next _ hs ih => exact .next ih ((step_reprice_iff input fee hfee C mode accounting tapes _ _ _).mpr hs)

theorem legalRule_reprice_iff (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) :
    LegalRule input C mode accounting policy ↔
      LegalRule (input.withCorrectionFee fee hfee) C mode accounting policy := by
  constructor <;> intro h seed truth tapes n s hp ha
  · obtain ⟨next, hs⟩ := h seed truth tapes n s
      ((prefix_reprice_iff input fee hfee C mode accounting policy seed truth tapes n s).mpr hp) ha
    exact ⟨next, (step_reprice_iff input fee hfee C mode accounting tapes _ _ _).mp hs⟩
  · obtain ⟨next, hs⟩ := h seed truth tapes n s
      ((prefix_reprice_iff input fee hfee C mode accounting policy seed truth tapes n s).mp hp) ha
    exact ⟨next, (step_reprice_iff input fee hfee C mode accounting tapes _ _ _).mpr hs⟩

theorem nextFromFrontier_reprice_eq (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (s : State I) (action : Action I) (frontier : Frontier input) :
    nextFromFrontier (input.withCorrectionFee fee hfee) C mode accounting s action frontier =
      nextFromFrontier input C mode accounting s action frontier := by
  by_cases hh : s.halted = true
  · simp [nextFromFrontier, hh]
  · have ha := Bool.eq_false_iff.mpr hh
    by_cases hex : ∃ next, Step input C mode accounting (frozenTapes input frontier) s action next
    · obtain ⟨next, hs⟩ := hex
      rw [nextFromFrontier_eq_of_step input C mode accounting s next action frontier ha hs,
        nextFromFrontier_eq_of_step (input.withCorrectionFee fee hfee) C mode accounting s next action frontier ha
          ((step_reprice_iff input fee hfee C mode accounting _ _ _ _).mp hs)]
    · have hex' : ¬ ∃ next, Step (input.withCorrectionFee fee hfee) C mode accounting
          (frozenTapes (input.withCorrectionFee fee hfee) frontier) s action next := by
        rintro ⟨next, hs⟩
        rw [frozenTapes_reprice_eq] at hs
        exact hex ⟨next, (step_reprice_iff input fee hfee C mode accounting _ _ _ _).mpr hs⟩
      simp only [nextFromFrontier, ha, Bool.false_eq_true, ↓reduceIte, dite_eq_right hex, dite_eq_right hex']

theorem run_reprice_eq (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (sample : Seed × input.World) (n : ℕ) :
    run (input.withCorrectionFee fee hfee) C mode accounting policy sample n =
      run input C mode accounting policy sample n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    exact nextFromFrontier_reprice_eq input fee hfee C mode accounting _ _ _

theorem runSuccess_reprice_iff (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (sample : Seed × input.World) :
    runSuccess (input.withCorrectionFee fee hfee) C mode accounting policy sample ↔
      runSuccess input C mode accounting policy sample := by
  simp only [runSuccess, run_reprice_eq]

theorem ledger_actualBill_mono_reprice (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (hmono : ∀ i r, input.correctionFee i r ≤ fee i r) (L : Ledger I) :
    L.actualBill input.fees ≤ L.actualBill (input.withCorrectionFee fee hfee).fees := by
  have hcorr : L.correctionBill input.fees ≤ L.correctionBill (input.withCorrectionFee fee hfee).fees := by
    unfold Ledger.correctionBill
    induction L.executions with
    | nil => exact le_rfl
    | cons e later ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (ENNReal.ofReal_le_ofReal (by exact_mod_cast hmono e.handle.stage e.tool)) ih
  exact add_le_add le_rfl hcorr

theorem runActualBill_mono_reprice (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (hmono : ∀ i r, input.correctionFee i r ≤ fee i r)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : PolicyRule I Seed) (sample : Seed × input.World) :
    runActualBill input C mode accounting policy sample ≤
      runActualBill (input.withCorrectionFee fee hfee) C mode accounting policy sample := by
  unfold runActualBill
  simp only [run_reprice_eq]
  exact iSup_mono (fun n => ledger_actualBill_mono_reprice input fee hfee hmono _)

section Measurable

variable [MeasurableSpace Seed]

@[simp] theorem seededWorldLaw_reprice_eq (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (ν : Measure Seed) :
    (input.withCorrectionFee fee hfee).seededWorldLaw ν = input.seededWorldLaw ν := rfl

def Policy.reprice (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed) :
    Policy (input.withCorrectionFee fee hfee) C mode accounting Seed where
  rule := policy.rule
  measurable_rule := policy.measurable_rule
  legal := (legalRule_reprice_iff input fee hfee C mode accounting policy.rule).mp policy.legal

def Policy.unprice (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : Policy (input.withCorrectionFee fee hfee) C mode accounting Seed) :
    Policy input C mode accounting Seed where
  rule := policy.rule
  measurable_rule := policy.measurable_rule
  legal := (legalRule_reprice_iff input fee hfee C mode accounting policy.rule).mpr policy.legal

theorem risk_reprice_eq (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (ν : Measure Seed) :
    risk (input.withCorrectionFee fee hfee) C mode accounting policy ν = risk input C mode accounting policy ν := by
  unfold risk
  rw [seededWorldLaw_reprice_eq]
  congr 1
  ext sample
  exact not_congr (runSuccess_reprice_iff input fee hfee C mode accounting policy sample)

theorem expectedObservationBill_reprice_eq (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (ν : Measure Seed) :
    expectedObservationBill (input.withCorrectionFee fee hfee) C mode accounting policy ν =
      expectedObservationBill input C mode accounting policy ν := by
  unfold expectedObservationBill
  rw [seededWorldLaw_reprice_eq]
  apply lintegral_congr
  intro sample
  unfold runObservationBill
  apply iSup_congr
  intro n
  exact congrArg (fun state : State I => state.ledger.observationBill input.fees)
    (run_reprice_eq input fee hfee C mode accounting policy sample n)

theorem expectedBill_mono_reprice (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (hmono : ∀ i r, input.correctionFee i r ≤ fee i r)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : PolicyRule I Seed) (ν : Measure Seed) :
    expectedBill input C mode accounting policy ν ≤
      expectedBill (input.withCorrectionFee fee hfee) C mode accounting policy ν :=
  lintegral_mono (runActualBill_mono_reprice input fee hfee hmono C mode accounting policy)

end Measurable

theorem value_mono_reprice (input : StatisticalInput I) (fee : I.Stage → I.Tool → ℚ)
    (hfee : ∀ i r, 0 ≤ fee i r) (hmono : ∀ i r, input.correctionFee i r ≤ fee i r)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I) (δ : ℝ≥0∞) :
    value input C mode accounting δ ≤ value (input.withCorrectionFee fee hfee) C mode accounting δ := by
  conv_rhs => unfold value
  refine le_iInf fun SmallSeed => le_iInf fun m => ?_
  let : MeasurableSpace SmallSeed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  let old := policy.val.unprice input fee hfee C mode accounting
  have hs : risk input C mode accounting old.rule ν ≤ δ := by
    change risk input C mode accounting policy.val.rule ν ≤ δ
    rw [← risk_reprice_eq input fee hfee C mode accounting policy.val.rule ν]
    exact policy.property
  exact (value_le_policy input C mode accounting δ ν old hs).trans
    (expectedBill_mono_reprice input fee hfee hmono C mode accounting policy.val.rule ν)

end Native
end PaperProofs.Common
