module

public import PaperProofs.Retained.Controller

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetAdministrativeClock003

open Common Common.Native

variable {I : Instance}

/-- Every non-informative protocol step consumes an actual commitment,
execution, stage advance, or the unique final halt. In particular, internal
shadow simulation cannot diverge while waiting for another observation or
write. Reports are retained as information and serials are erased only by
the existing R02 informationTrace definition. -/
theorem prefix_clock_accounting (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    n + (if s.halted then 0 else 1) ≤ (informationTrace s.history).length +
      s.ledger.commitments.length + s.ledger.executions.length + s.cursor + 1 := by
  induction hp with
  | initial => simp [initial, informationTrace]
  | @next n s s' hp step ih =>
    have hactive := step_source_active input C mode accounting tapes step
    simp only [hactive, Bool.false_eq_true, ↓reduceIte] at ih
    simp only [informationTrace] at ih
    generalize haction : rule seed s.history = action at step
    cases step <;>
      simp [record, stopState, informationTrace, informationEvent, List.filterMap_append,
        writeResponses, reportedWriteLedger, hearly, writeLedger, reviewLedger,
        allocateLedger, executeLedger, advanceLedger, List.length_append] <;> omega

/-- A uniform finite search bound for replaying a real source prefix from
its information record. It does not depend on resource caps, accounting
values, success, finite expected cost, or a termination hypothesis. -/
theorem prefix_clock_le_information (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    n ≤ (informationTrace s.history).length + I.stageCount + 2 * I.toolCount + 1 := by
  have hc := prefix_clock_accounting input C hearly mode accounting rule seed truth tapes hp
  have hwf := prefix_ledgerWellFormed input C mode accounting rule seed truth tapes hp
  have hcommit : s.ledger.commitments.length ≤ I.toolCount := by
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hwf.commitment_tools.length_le_card
  have hexecute : s.ledger.executions.length ≤ I.toolCount := by
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hwf.execution_tools.length_le_card
  have hcursor := (prefix_cursorInvariant input C mode accounting rule seed truth tapes hp).bound
  omega

end PaperProofs.Retained.PRetAdministrativeClock003
