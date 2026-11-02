module

public import PaperProofs.Paid.PDMenu_CurrentReplayPaidCharge_026

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*}

/-- Once an execution was physically made, its real fee adds to ALL
observation spending, including spending on failed/nonreturn paths. -/
theorem runObservationBill_add_actualFee_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (clock : ℕ) (e : Execution I) (he : e ∈ (run input C mode accounting rule sample clock).ledger.executions)
    (fee : ℚ) (hfee : ∀ stage tool, input.fees.correction stage tool = fee) :
    runObservationBill input C mode accounting rule sample + ENNReal.ofReal (fee : ℝ) ≤
      runActualBill input C mode accounting rule sample := by
  change (⨆ t, (run input C mode accounting rule sample t).ledger.observationBill input.fees) + _ ≤ _
  rw [ENNReal.iSup_add]
  apply iSup_le
  intro t
  let later := run input C mode accounting rule sample (clock + t)
  have heLater : e ∈ later.ledger.executions := run_execution_preserved input C mode accounting rule hlegal sample clock t e he
  have hlen : 1 ≤ later.ledger.executions.length := by
    cases hlist : later.ledger.executions with
    | nil => rw [hlist] at heLater; cases heLater
    | cons first rest => simp only [List.length_cons, Nat.succ_le_succ_iff, Nat.zero_le]
  have hcorr : ENNReal.ofReal (fee : ℝ) ≤ later.ledger.correctionBill input.fees := by
    rw [correctionBill_constant _ fee hfee]
    calc
      _ = 1 * ENNReal.ofReal (fee : ℝ) := (one_mul _).symm
      _ ≤ _ := by
        have hlenENN : (1 : ℝ≥0∞) ≤ (later.ledger.executions.length : ℝ≥0∞) := by exact_mod_cast hlen
        exact mul_le_mul_left hlenENN (ENNReal.ofReal (fee : ℝ))
  have hobs : (run input C mode accounting rule sample t).ledger.observationBill input.fees ≤
      later.ledger.observationBill input.fees := by
    calc
      _ ≤ (run input C mode accounting rule sample t).ledger.observationBill input.fees +
          observationIncrement input (run input C mode accounting rule sample t) later := le_self_add
      _ = _ := (observationBill_eq_prefix_add_increment input _ _
        (fun stage => run_reviews_mono input C mode accounting rule hlegal sample stage (Nat.le_add_left t clock))).symm
  exact (add_le_add hobs hcorr).trans (prefixBill_le_runActualBill input C mode accounting rule sample (clock + t))

end PDMenu

