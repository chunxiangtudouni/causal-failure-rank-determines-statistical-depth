module

public import PaperProofs.Common.NativeRun
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Finset.Lattice.Fold

/-!
Uniform bounds on actual correction charges, on every path, including failure
and nontermination. The maximum ranges over the input's compatible pairs; an
empty compatibility relation gives zero. No finite observation expectation or
resource certificate is assumed, and pending commitments are never charged.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PaperProofs.Common

variable {I : Instance}

def Instance.compatiblePairs (I : Instance) : Finset (I.Stage × I.Tool) :=
  Finset.univ.filter (fun pair => pair.2 ∈ I.eligible pair.1)

theorem Instance.mem_compatiblePairs (I : Instance) (i : I.Stage) (r : I.Tool) :
    (i, r) ∈ I.compatiblePairs ↔ r ∈ I.eligible i := by
  simp [Instance.compatiblePairs]

noncomputable def Fees.maxCorrection (F : Fees I) : ℝ≥0∞ :=
  I.compatiblePairs.sup (fun pair => ENNReal.ofReal (F.correction pair.1 pair.2 : ℝ))

theorem Fees.correction_le_max (F : Fees I) (i : I.Stage) (r : I.Tool)
    (hcompatible : r ∈ I.eligible i) :
    ENNReal.ofReal (F.correction i r : ℝ) ≤ F.maxCorrection := by
  unfold Fees.maxCorrection
  exact Finset.le_sup (f := fun pair : I.Stage × I.Tool =>
    ENNReal.ofReal (F.correction pair.1 pair.2 : ℝ))
      ((I.mem_compatiblePairs i r).mpr hcompatible)

theorem Fees.maxCorrection_lt_top (F : Fees I) : F.maxCorrection < ⊤ := by
  apply (Finset.sup_lt_iff (show (⊥ : ℝ≥0∞) < ⊤ from bot_lt_top)).mpr
  intro pair _
  exact ENNReal.ofReal_lt_top

theorem Fees.maxCorrection_eq_zero_of_no_pairs (F : Fees I)
    (hempty : I.compatiblePairs = ∅) : F.maxCorrection = 0 := by
  simp [Fees.maxCorrection, hempty]

theorem Ledger.correctionBill_le_length_max {L : Ledger I} (h : LedgerWellFormed L)
    (F : Fees I) : L.correctionBill F ≤ (L.executions.length : ℝ≥0∞) * F.maxCorrection := by
  have hsum := List.sum_le_length_nsmul
    (L.executions.map (fun e => ENNReal.ofReal (F.correction e.handle.stage e.tool : ℝ)))
    F.maxCorrection (by
      intro fee hfee
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hfee
      exact F.correction_le_max e.handle.stage e.tool (h.compatible e he))
  simpa only [Ledger.correctionBill, List.length_map, nsmul_eq_mul] using hsum

theorem Ledger.correctionBill_le_max {L : Ledger I} (h : LedgerWellFormed L)
    (F : Fees I) :
    L.correctionBill F ≤ (min I.stageCount I.toolCount : ℕ) * F.maxCorrection := by
  exact (Ledger.correctionBill_le_length_max h F).trans
    (mul_le_mul_left (by exact_mod_cast Ledger.execution_count_le h) F.maxCorrection)

namespace Native

variable {Seed : Type*}

noncomputable def runObservationBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) : ℝ≥0∞ :=
  ⨆ n, (run input C mode accounting policy sample n).ledger.observationBill input.fees

theorem runObservationBill_le_actual (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) :
    runObservationBill input C mode accounting policy sample ≤
      runActualBill input C mode accounting policy sample := by
  apply iSup_le
  intro n
  exact ((run input C mode accounting policy sample n).ledger.observationBill_le_actualBill
    input.fees).trans (prefixBill_le_runActualBill input C mode accounting policy sample n)

theorem runActualBill_le_observation_add (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World) :
    runActualBill input C mode accounting policy sample ≤
      runObservationBill input C mode accounting policy sample +
        (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  apply iSup_le
  intro n
  apply add_le_add
  · exact le_iSup (fun k : ℕ =>
      (run input C mode accounting policy sample k).ledger.observationBill input.fees) n
  · exact Ledger.correctionBill_le_max
      (run_ledgerWellFormed input C mode accounting policy hlegal sample n) input.fees

section Measurable

variable [MeasurableSpace Seed]

theorem measurable_runObservationBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hpolicy : MeasurableRule policy) :
    Measurable (runObservationBill input C mode accounting policy) := by
  apply Measurable.iSup
  intro n
  exact (measurable_of_countable (fun s : State I =>
    s.ledger.observationBill input.fees)).comp
      (measurable_run input C mode accounting policy hpolicy n)

noncomputable def expectedObservationBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (ν : Measure Seed) : ℝ≥0∞ :=
  ∫⁻ sample, runObservationBill input C mode accounting policy sample ∂input.seededWorldLaw ν

theorem expectedObservationBill_le_actual (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (ν : Measure Seed) :
    expectedObservationBill input C mode accounting policy ν ≤
      expectedBill input C mode accounting policy ν :=
  lintegral_mono (runObservationBill_le_actual input C mode accounting policy)

theorem expectedBill_le_observation_add (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    expectedBill input C mode accounting policy.rule ν ≤
      expectedObservationBill input C mode accounting policy.rule ν +
        (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  have hmono := lintegral_mono
    (runActualBill_le_observation_add input C mode accounting policy.rule policy.legal)
      (μ := input.seededWorldLaw ν)
  rw [lintegral_add_left (measurable_runObservationBill input C mode accounting
    policy.rule policy.measurable_rule)] at hmono
  simpa only [expectedBill, expectedObservationBill, lintegral_const, measure_univ, mul_one]
    using hmono

end Measurable
end Native
end PaperProofs.Common
