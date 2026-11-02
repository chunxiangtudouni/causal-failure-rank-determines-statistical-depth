module

public import PaperProofs.Paid.PDROC_SimulatorLaw_012
public import PaperProofs.Paid.PDROC_StageExit_002
public import PaperProofs.Paid.PDROC_Simulator_044
public import PaperProofs.Common.ReferenceGlobalCost

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

/-- The old optional entry is retained in the kernel seed. A missing prior
entry can never create a later entry through an analysis completion. -/
def simulatorNextEntryProjection (next : I.Stage)
    (result : (Seed × EntryHistory I) × List (VisibleEvent I)) : Seed × EntryHistory I :=
  (result.1.1, if result.1.2.isSome = true ∧ historyHalted result.2 = false ∧
    historyCursor result.2 = next.val then some result.2 else none)

theorem measurable_simulatorNextEntryProjection [MeasurableSpace Seed] (next : I.Stage) :
    Measurable (simulatorNextEntryProjection (Seed := Seed) next) := by
  have hm : Measurable (fun pair : EntryHistory I × List (VisibleEvent I) =>
      if pair.1.isSome = true ∧ historyHalted pair.2 = false ∧ historyCursor pair.2 = next.val
      then some pair.2 else none) := measurable_of_countable _
  exact (measurable_fst.comp measurable_fst).prodMk
    (hm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem simulatorNextEntryProjection_prior_none (next : I.Stage) (seed : Seed)
    (exit : List (VisibleEvent I)) :
    simulatorNextEntryProjection next ((seed, none), exit) = (seed, none) := by
  simp only [simulatorNextEntryProjection, Option.isSome_none, Bool.false_eq_true,
    false_and, ↓reduceIte]

theorem simulatorNextEntryProjection_active_next (next : I.Stage) (seed : Seed)
    (entry exit : List (VisibleEvent I)) (hh : historyHalted exit = false)
    (hc : historyCursor exit = next.val) :
    simulatorNextEntryProjection next ((seed, some entry), exit) = (seed, some exit) := by
  simp only [simulatorNextEntryProjection, Option.isSome_some, hh, hc, and_self, ↓reduceIte]

theorem simulatorNextEntryProjection_halted (next : I.Stage) (seed : Seed)
    (prior : EntryHistory I) (exit : List (VisibleEvent I)) (hh : historyHalted exit = true) :
    simulatorNextEntryProjection next ((seed, prior), exit) = (seed, none) := by
  simp only [simulatorNextEntryProjection, hh, Bool.true_eq_false, false_and, and_false, ↓reduceIte]

theorem entryHistory_next_none_of_prior_none (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hl : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (stage next : I.Stage) (hle : stage.val ≤ next.val)
    (hnone : entryHistory input C mode accounting source stage sample = none) :
    entryHistory input C mode accounting source next sample = none := by
  apply (entryHistory_none_iff input C mode accounting source next sample).mpr
  rintro ⟨n, hn⟩
  have hlt := run_cursor_lt_of_no_entry input C mode accounting source hl sample stage hnone n
  rw [hn] at hlt
  omega

end PDROC
