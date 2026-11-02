module

public import PaperProofs.Retained.PRet_InformationPackets_006
public import PaperProofs.Common.HistorySuffixWorld

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryReplay045

open Common Common.Native MeasureTheory PRetPublicAdministrativeReplay005 PRetInformationPackets006

variable {I : Instance}

/-- Restart the already-proved public administration at a genuine PUBLIC
entry snapshot. No hidden truth/tape is part of the restart arguments. -/
noncomputable def replayFrom {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (startup : Startup I) (packets : List (Packet I)) : Option (Startup I) :=
  packets.foldlM (consume accounting source seed)
    (settle accounting source (I.stageCount + 2 * I.toolCount + 2) seed startup).1

def liftPacket (first : ℕ) : Packet (I.freshSuffix first) → Packet I
  | .review stage symbol => .review (I.freshStageLift first stage) symbol
  | .write stage bit truth => .write (I.freshStageLift first stage) bit truth

/-- Only actual fresh review/write/early-report information is lifted into
the original entry snapshot. The original source rule/serials/accounting
remain those of the full original input. -/
noncomputable def shadowFrom {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (startup : Startup I) (seed : Seed)
    (history : List (VisibleEvent (I.freshSuffix first))) : Option (Startup I) := do
  let packets ← parse (informationTrace history)
  replayFrom accounting source seed startup (packets.map (liftPacket first))

theorem replayFrom_information {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (startup final : Startup I) (packets : List (Packet I))
    (hr : replayFrom accounting source seed startup packets = some final) :
    informationTrace final.history = informationTrace startup.history ++ packets.flatMap Packet.events := by
  have hi := fold_packets_information accounting source seed packets _ final hr
  rw [settle_information] at hi
  exact hi

theorem replayFrom_initial_actual {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World) (n : ℕ) :
    ∃ later ≥ n, replayFrom accounting source sample.1
      (publicStartup (run input C mode accounting source sample n)) [] =
        some (publicStartup (run input C mode accounting source sample later)) := by
  let result := settle accounting source (I.stageCount + 2 * I.toolCount + 2) sample.1
    (publicStartup (run input C mode accounting source sample n))
  refine ⟨n + result.2, Nat.le_add_right _ _, ?_⟩
  exact congrArg some (settle_actual input C mode accounting source hlegal sample
    (I.stageCount + 2 * I.toolCount + 2) n)

section Measurable

variable {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_replayFrom (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hsource : MeasurableRule source) (packets : List (Packet I)) :
    Measurable (fun sample : Seed × Startup I => replayFrom accounting source sample.1 sample.2 packets) := by
  have hs := measurable_settle accounting source hsource (I.stageCount + 2 * I.toolCount + 2)
  have hstarted := measurable_fst.comp hs
  exact (measurable_fold_packets accounting source hsource packets).comp (measurable_fst.prodMk hstarted)

theorem measurable_shadowFrom (first : ℕ) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hsource : MeasurableRule source) (startup : Startup I) :
    Measurable (fun sample : Seed × List (VisibleEvent (I.freshSuffix first)) =>
      shadowFrom first accounting source startup sample.1 sample.2) := by
  apply measurable_from_prod_countable_left
  intro history
  cases hp : parse (informationTrace history) with
  | none =>
    simpa only [shadowFrom, hp, Option.bind_eq_bind, Option.bind_none] using
      (measurable_const (a := (none : Option (Startup I))) : Measurable (fun _ : Seed => none))
  | some packets =>
    have hm : Measurable (fun seed : Seed =>
        replayFrom accounting source seed startup (packets.map (liftPacket first))) :=
      (measurable_replayFrom accounting source hsource (packets.map (liftPacket first))).comp
        (measurable_id.prodMk (measurable_const (a := startup)))
    simpa only [shadowFrom, hp, Option.bind_eq_bind, Option.bind_some] using
      hm

end Measurable

end PaperProofs.Retained.PRetEntryReplay045
