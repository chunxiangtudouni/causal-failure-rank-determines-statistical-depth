module

public import PaperProofs.Paid.PDMenu_MenuNativeRecordABI_114
public import PaperProofs.Paid.PDMenu_MenuRepairRecords_109
public import PaperProofs.Paid.PDMenu_MenuPastPhysical_100
public import PaperProofs.Paid.PDMenu_MenuEntryBranches_112
public import PaperProofs.Paid.PDMenu_MenuSummaryBranches_113

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Induction conclusion for a genuine arbitrary entry in the original
physical machine. It is an exact path record target, not an assumed field
of a continuation Policy or a supplied expected-performance assertion. -/
def MenuEntryRunRecords (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K))
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + n = N) : Prop :=
  let start := run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock
  let record := menuPathSummary P table n (K - start.ledger.executions.length)
    (menuSuffixSeed N K cursor n hfit sample.1) (menuSuffixWorld P N K cursor n hfit fee hfee sample.2)
  ∃ ended : ℕ, clock ≤ ended ∧
    (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample ended).halted = true ∧
    (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample ended).ledger.observationBill (P.freshInput N K fee hfee).fees =
      start.ledger.observationBill (P.freshInput N K fee hfee).fees + record.observation ∧
    (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample ended).ledger.executions.length =
      start.ledger.executions.length + record.physicalRepairs ∧
    (runSuccess (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample ↔ record.failure = false)

/-- Once the real entry induction is proved, its root case gives precisely
the stable Native agreement ABI consumed by the expectation transfer. -/
theorem menuNativePathAgreement_of_root_records (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (hrecords : MenuEntryRunRecords P N K table fee hfee C accounting sample 0 N 0 (Nat.zero_add N)) :
    MenuNativePathAgreement P N K table fee hfee C accounting sample := by
  obtain ⟨ended, _, hhalt, hobs, hrep, hsuccess⟩ := hrecords
  have hlegal := P.compiledMenuRule_uncapped_legal N K table fee hfee C hearly accounting
  have hobs' := menu_runObservationBill_of_halted (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) hlegal sample ended hhalt
  have hrep' := menu_runRepairCount_of_halted (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) sample ended hhalt
  have hroot : K - (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample 0).ledger.executions.length = K := rfl
  rw [hroot, menuSuffixSeed_root, menuSuffixWorld_root] at hobs hrep hsuccess
  have hobs0 : (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample 0).ledger.observationBill
      (P.freshInput N K fee hfee).fees = 0 := by
    simp only [run, initial, Ledger.observationBill, ENat.toENNReal_zero, mul_zero, Finset.sum_const_zero]
  rw [hobs0, zero_add] at hobs
  have hrep0 : (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample 0).ledger.executions.length = 0 := rfl
  rw [hrep0, Nat.zero_add] at hrep
  exact ⟨hobs'.trans hobs, hrep'.trans (congrArg (fun n : ℕ => (n : ℝ≥0∞)) hrep), hsuccess⟩

end PDMenu
