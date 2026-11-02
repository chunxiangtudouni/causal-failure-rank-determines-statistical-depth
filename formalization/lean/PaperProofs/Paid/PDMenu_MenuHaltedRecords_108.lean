module

public import PaperProofs.Paid.PDMenu_MenuBillCount_072
public import PaperProofs.Common.NativeHeadAccounting

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

theorem menu_runObservationBill_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (clock : ℕ) (hhalt : (run input C mode accounting rule sample clock).halted = true) :
    runObservationBill input C mode accounting rule sample =
      (run input C mode accounting rule sample clock).ledger.observationBill input.fees := by
  rw [runObservationBill_eq_prefix_add_future input C mode accounting rule hlegal sample clock,
    futureObservationBill_of_halted input C mode accounting rule sample clock hhalt, add_zero]

/-- The supremum counts all earlier physical executions, including on an
abandoned path; it is exactly the stabilized original ledger count. -/
theorem menu_runRepairCount_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (clock : ℕ)
    (hhalt : (run input C mode accounting rule sample clock).halted = true) :
    runRepairCount input C mode accounting rule sample =
      ((run input C mode accounting rule sample clock).ledger.executions.length : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hle : k ≤ clock
    · exact_mod_cast PDROC.run_executionCount_mono input C mode accounting rule sample hle
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge hle)
      rw [run_after_halt input C mode accounting rule sample clock hhalt extra]
  · exact le_iSup (fun n => ((run input C mode accounting rule sample n).ledger.executions.length : ℝ≥0∞)) clock

theorem menu_runSuccess_iff_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (clock : ℕ)
    (hhalt : (run input C mode accounting rule sample clock).halted = true) :
    runSuccess input C mode accounting rule sample ↔
      (run input C mode accounting rule sample clock).ledger.success C := by
  constructor
  · rintro ⟨other, hother, hsuccess⟩
    rcases le_total other clock with hle | hle
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [run_after_halt input C mode accounting rule sample other hother extra]
      exact hsuccess
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [run_after_halt input C mode accounting rule sample clock hhalt extra] at hsuccess
      exact hsuccess
  · exact fun hsuccess => ⟨clock, hhalt, hsuccess⟩

end PDMenu
