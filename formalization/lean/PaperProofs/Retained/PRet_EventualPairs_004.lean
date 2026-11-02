module

public import PaperProofs.Retained.Controller

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEventualPairs004

open Common Common.Native MeasureTheory

variable {I : Instance}

theorem mem_eventualPairs {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (pair : I.Stage × I.Tool) :
    pair ∈ eventualPairs input C mode accounting rule sample ↔
      ∃ n, ∃ e ∈ (run input C mode accounting rule sample n).ledger.executions,
        e.handle.stage = pair.1 ∧ e.tool = pair.2 := by
  classical
  simp only [eventualPairs, Finset.mem_filter, Finset.mem_univ, true_and]

/-- R02's complete eventual-pair random variable is measurable on every
actual source world, including abandoned and nonreturning runs. No finite
expected bill or success restriction is used. -/
theorem measurable_eventualPairs {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hrule : MeasurableRule rule) :
    Measurable (eventualPairs input C mode accounting rule) := by
  apply measurable_finset_iff.mpr
  intro pair
  apply measurableSet_setOfPred.mp
  have heq : {sample : Seed × input.World | pair ∈ eventualPairs input C mode accounting rule sample} =
      ⋃ n : ℕ, {sample : Seed × input.World |
        ∃ e ∈ (run input C mode accounting rule sample n).ledger.executions,
          e.handle.stage = pair.1 ∧ e.tool = pair.2} := by
    ext sample
    simp only [mem_eventualPairs, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact (measurable_run input C mode accounting rule hrule n)
    (MeasurableSpace.measurableSet_top (s := {s : State I |
      ∃ e ∈ s.ledger.executions, e.handle.stage = pair.1 ∧ e.tool = pair.2}))

end PaperProofs.Retained.PRetEventualPairs004
