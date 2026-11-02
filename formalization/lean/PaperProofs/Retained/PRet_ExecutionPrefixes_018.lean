module

public import PaperProofs.Retained.PRet_InformationPackets_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetExecutionPrefixes018

open Common Common.Native PRetPublicAdministrativeReplay005 PRetInformationPackets006

variable {I : Instance}

theorem silentNext_executions_prefix (accounting : NormalAccounting I) (startup next : Startup I) (action : Action I)
    (hn : silentNext accounting startup action = some next) :
    startup.executions.IsPrefix next.executions := by
  obtain ⟨_, ha, rfl⟩ := (silentNext_some_iff accounting startup next action).mp hn
  cases action <;> simp_all [silentAction, silentUpdate, Startup.allocatePublic,
    Startup.executePublic, Startup.advancePublic, Startup.stopPublic]

theorem settle_executions_prefix {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (fuel : ℕ) (seed : Seed) (startup : Startup I) :
    startup.executions.IsPrefix (settle accounting source fuel seed startup).1.executions := by
  induction fuel generalizing startup with
  | zero => exact List.prefix_rfl
  | succ fuel ih =>
    generalize hn : silentNext accounting startup (source seed startup.history) = next
    cases next with
    | none => simp only [settle, hn]; exact List.prefix_rfl
    | some next =>
      simp only [settle, hn]
      exact (silentNext_executions_prefix accounting startup next _ hn).trans (ih next)

theorem consume_executions_prefix {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (startup next : Startup I) (packet : Packet I)
    (hconsume : consume accounting source seed startup packet = some next) :
    startup.executions.IsPrefix next.executions := by
  unfold consume at hconsume
  split at hconsume
  · have heq := Option.some.inj hconsume
    subst next
    have hp := settle_executions_prefix accounting source (I.stageCount + 2 * I.toolCount + 2) seed
      (packet.applyPublic accounting startup)
    cases packet <;> simpa only [Packet.applyPublic, Startup.reviewPublic, Startup.writePublic] using hp
  · cases hconsume

end PaperProofs.Retained.PRetExecutionPrefixes018
