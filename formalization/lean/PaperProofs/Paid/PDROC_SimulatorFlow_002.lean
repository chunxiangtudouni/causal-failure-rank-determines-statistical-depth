module

public import PaperProofs.Paid.PDROC_SimulatorFlow_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v
variable {I : Instance} {Seed : Type u} {OldSeed : Type v}

theorem entryHistory_none_of_halted_minimal_stage_exit (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hl : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (start offset : ℕ) (stage next : I.Stage) (hnext : next.val = stage.val + 1)
    (hc : (run input C mode accounting source sample start).cursor = stage.val)
    (hbefore : ∀ k < offset, (run input C mode accounting source sample (start + k)).cursor = stage.val)
    (hh : (run input C mode accounting source sample (start + offset)).halted = true) :
    entryHistory input C mode accounting source next sample = none := by
  have hne : (run input C mode accounting source sample (start + offset)).cursor ≠ next.val := by
    intro he
    have hf := firstEntryAt_of_minimal_stage_exit input C mode accounting source hl sample start offset stage next hnext hc he hbefore
    have ha := (firstEntryAt_unborn input C mode accounting source hl sample next.val (start + offset) hf).1
    rw [hh] at ha
    cases ha
  apply (entryHistory_none_iff input C mode accounting source next sample).mpr
  rintro ⟨n, hn⟩
  by_cases hnf : n < start + offset
  · by_cases hns : n ≤ start
    · have hm := run_cursor_monotone input C mode accounting source hl sample hns
      change (run input C mode accounting source sample n).cursor ≤
        (run input C mode accounting source sample start).cursor at hm
      rw [hc, hn] at hm
      omega
    · have hb := hbefore (n - start) (by omega)
      rw [show start + (n - start) = n by omega, hn] at hb
      omega
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (by omega : start + offset ≤ n)
    rw [run_after_halt input C mode accounting source sample (start + offset) hh extra] at hn
    exact hne hn

/-- A minimal genuine exit determines the eventual next entry, including
all early-halt branches, after any cursor/halt-preserving history map. -/
theorem entryHistory_map_projection_of_minimal_stage_exit (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hl : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (start offset : ℕ) (stage next : I.Stage) (hnext : next.val = stage.val + 1)
    (hc : (run input C mode accounting source sample start).cursor = stage.val)
    (hbefore : ∀ k < offset, (run input C mode accounting source sample (start + k)).cursor = stage.val)
    (hexit : (run input C mode accounting source sample (start + offset)).halted = true ∨
      (run input C mode accounting source sample (start + offset)).cursor = stage.val + 1)
    (shadow : List (VisibleEvent I) → List (VisibleEvent I))
    (hh : historyHalted (shadow (run input C mode accounting source sample (start + offset)).history) =
      (run input C mode accounting source sample (start + offset)).halted)
    (hcursor : historyCursor (shadow (run input C mode accounting source sample (start + offset)).history) =
      (run input C mode accounting source sample (start + offset)).cursor)
    (oldSeed : OldSeed) (prior : List (VisibleEvent I)) :
    (oldSeed, (entryHistory input C mode accounting source next sample).map shadow) =
      simulatorNextEntryProjection next ((oldSeed, some prior),
        shadow (run input C mode accounting source sample (start + offset)).history) := by
  by_cases hhalt : (run input C mode accounting source sample (start + offset)).halted = true
  · rw [entryHistory_none_of_halted_minimal_stage_exit input C mode accounting source hl sample
      start offset stage next hnext hc hbefore hhalt, Option.map_none]
    exact (simulatorNextEntryProjection_halted next oldSeed (some prior) _ (hh.trans hhalt)).symm
  · have ha : (run input C mode accounting source sample (start + offset)).halted = false :=
      Bool.eq_false_iff.mpr hhalt
    have he : (run input C mode accounting source sample (start + offset)).cursor = next.val :=
      (hexit.resolve_left hhalt).trans hnext.symm
    rw [entryHistory_of_minimal_stage_exit input C mode accounting source hl sample
      start offset stage next hnext hc he hbefore, Option.map_some]
    exact (simulatorNextEntryProjection_active_next next oldSeed prior _ (hh.trans ha) (hcursor.trans he)).symm

theorem entryHistory_map_projection_of_no_prior_entry (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hl : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (stage next : I.Stage) (hle : stage.val ≤ next.val)
    (hnone : entryHistory input C mode accounting source stage sample = none)
    (shadow : List (VisibleEvent I) → List (VisibleEvent I)) (oldSeed : OldSeed) (exit : List (VisibleEvent I)) :
    (oldSeed, (entryHistory input C mode accounting source next sample).map shadow) =
      simulatorNextEntryProjection next ((oldSeed, none), exit) := by
  rw [entryHistory_next_none_of_prior_none input C mode accounting source hl sample stage next hle hnone,
    Option.map_none, simulatorNextEntryProjection_prior_none]

end PDROC
