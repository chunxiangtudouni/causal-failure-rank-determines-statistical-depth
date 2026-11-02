module

public import PaperProofs.Common.HistorySuffixCharge
public import PaperProofs.Common.NativeHeadAccounting
public import PaperProofs.Retained.Controller

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFutureBillDecomposition086

open Common Common.Native
open scoped ENNReal

variable {I : Instance}

theorem firstEntry_increment_eq_futureFilter {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (first start now : ℕ) (hentry : FirstEntryAt input C mode accounting source first start sample) (hnow : start ≤ now) :
    observationIncrement input (run input C mode accounting source sample start) (run input C mode accounting source sample now) =
      ∑ stage ∈ Finset.univ.filter (fun stage : I.Stage => first ≤ stage.val),
        ENNReal.ofReal (input.fees.observation stage : ℝ) *
          ((run input C mode accounting source sample now).ledger.reviews stage : ℝ≥0∞) := by
  classical
  rw [firstEntry_observationIncrement_eq_future_sum input C mode accounting source hlegal sample first start now hentry hnow,
    Finset.sum_filter, sum_referenceSuffix_stages]

/-- Actual post-entry future charges equal the source's complete future-stage
review suprema, also on failed/nonreturn paths and at infinite cost. -/
theorem runFutureBill_eq_futureObservationBill {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C mode accounting source first start sample) :
    runFutureObservationBill input C mode accounting source first sample =
      futureObservationBill input C mode accounting source start sample := by
  classical
  let g := fun n => ∑ stage ∈ Finset.univ.filter (fun stage : I.Stage => first ≤ stage.val),
    ENNReal.ofReal (input.fees.observation stage : ℝ) *
      ((run input C mode accounting source sample n).ledger.reviews stage : ℝ≥0∞)
  have hmono : Monotone g := by
    intro a b hab
    apply Finset.sum_le_sum
    intro stage _
    exact mul_le_mul_right (ENat.toENNReal_mono (run_reviews_mono input C mode accounting source hlegal sample stage hab)) _
  have hprefix (extra : ℕ) : observationIncrement input (run input C mode accounting source sample start)
      (run input C mode accounting source sample (start + extra)) = g (start + extra) :=
    firstEntry_increment_eq_futureFilter input C mode accounting source hlegal sample first start (start + extra)
      hentry (Nat.le_add_right _ _)
  change (⨆ n, g n) = ⨆ extra, observationIncrement input (run input C mode accounting source sample start)
    (run input C mode accounting source sample (start + extra))
  simp_rw [hprefix]
  apply le_antisymm
  · apply iSup_le
    intro n
    exact (hmono (Nat.le_add_left n start)).trans (le_iSup (fun extra => g (start + extra)) n)
  · apply iSup_le
    intro extra
    exact le_iSup g (start + extra)

theorem runObservationBill_eq_entry_add_futureFilter {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C mode accounting source first start sample) :
    runObservationBill input C mode accounting source sample =
      (run input C mode accounting source sample start).ledger.observationBill input.fees +
        runFutureObservationBill input C mode accounting source first sample := by
  rw [runFutureBill_eq_futureObservationBill input C mode accounting source hlegal sample first start hentry]
  exact runObservationBill_eq_prefix_add_future input C mode accounting source hlegal sample start

end PaperProofs.Retained.PRetFutureBillDecomposition086
