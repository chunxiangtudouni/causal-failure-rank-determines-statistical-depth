module

public import PaperProofs.Paid.PDROC_StageExit_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {Seed : Type*}

/-- Minimal stage exit is the genuine first entry to the next stage. The
prefix before the selected start is covered by original cursor monotonicity. -/
theorem firstEntryAt_of_minimal_stage_exit (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hl : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (start exit : ℕ) (stage next : I.Stage)
    (hnext : next.val = stage.val + 1)
    (hc : (run input C mode accounting source sample start).cursor = stage.val)
    (hexit : (run input C mode accounting source sample (start + exit)).cursor = next.val)
    (hbefore : ∀ k < exit, (run input C mode accounting source sample (start + k)).cursor = stage.val) :
    FirstEntryAt input C mode accounting source next.val (start + exit) sample := by
  refine ⟨hexit, ?_⟩
  intro k hk
  by_cases hks : k ≤ start
  · have hmono := run_cursor_monotone input C mode accounting source hl sample hks
    change (run input C mode accounting source sample k).cursor ≤
      (run input C mode accounting source sample start).cursor at hmono
    rw [hc] at hmono
    omega
  · have hlocal : k - start < exit := by omega
    have hcursor := hbefore (k - start) hlocal
    rw [show start + (k - start) = k by omega] at hcursor
    omega

theorem entryHistory_of_minimal_stage_exit (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hl : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (start exit : ℕ) (stage next : I.Stage)
    (hnext : next.val = stage.val + 1)
    (hc : (run input C mode accounting source sample start).cursor = stage.val)
    (hexit : (run input C mode accounting source sample (start + exit)).cursor = next.val)
    (hbefore : ∀ k < exit, (run input C mode accounting source sample (start + k)).cursor = stage.val) :
    entryHistory input C mode accounting source next sample =
      some (run input C mode accounting source sample (start + exit)).history := by
  have he := firstEntryAt_of_minimal_stage_exit input C mode accounting source hl sample start exit stage next hnext hc hexit hbefore
  exact (entryHistory_some_iff input C mode accounting source next sample _).mpr ⟨start + exit, he.1, he.2, rfl⟩

end PDROC
