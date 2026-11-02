module

public import PaperProofs.Retained.PRet_InformationPackets_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetShadowInitial012

open Common Common.Native PRetPublicAdministrativeReplay005 PRetInformationPackets006

variable {I : Instance}

theorem shadow_congr {Seed : Type*} (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed)
    (seed : Seed) (first later : List (VisibleEvent I))
    (hinfo : informationTrace first = informationTrace later) :
    shadow accounting sourceRule seed first = shadow accounting sourceRule seed later := by
  unfold shadow
  rw [hinfo]

/-- The empty target history reconstructs a genuine source prefix on EVERY
same-world source sample, although the pure reconstruction has no world
argument. The old prefix may already have stopped or abandoned. -/
theorem shadow_nil_actual {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting sourceRule) (sample : Seed × input.World) :
    ∃ oldClock ≤ I.stageCount + 2 * I.toolCount + 2,
      shadow accounting sourceRule sample.1 [] =
        some (publicStartup (run input C mode accounting sourceRule sample oldClock)) := by
  let fuel := I.stageCount + 2 * I.toolCount + 2
  let empty := publicStartup (initial (I := I) (fun _ => false))
  let result := settle accounting sourceRule fuel sample.1 empty
  have hcount : result.2 ≤ fuel := settle_count_le accounting sourceRule fuel sample.1 empty
  have hactual := settle_actual input C mode accounting sourceRule hlegal sample fuel 0
  have hinitial : publicStartup (run input C mode accounting sourceRule sample 0) = empty := rfl
  rw [hinitial] at hactual
  change result.1 = publicStartup (run input C mode accounting sourceRule sample (0 + result.2)) at hactual
  refine ⟨result.2, hcount, ?_⟩
  change some result.1 = some (publicStartup (run input C mode accounting sourceRule sample result.2))
  exact congrArg some (by simpa only [Nat.zero_add] using hactual)

end PaperProofs.Retained.PRetShadowInitial012
