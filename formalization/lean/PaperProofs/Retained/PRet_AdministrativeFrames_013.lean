module

public import PaperProofs.Retained.PRet_PublicAdministrativeReplay_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetAdministrativeFrames013

open Common Common.Native PRetPublicAdministrativeReplay005

variable {I : Instance}

theorem silentNext_frames (accounting : NormalAccounting I) (startup next : Startup I) (action : Action I)
    (hn : silentNext accounting startup action = some next) :
    next.reviews = startup.reviews ∧ next.written = startup.written ∧
      next.writeSerial = startup.writeSerial ∧ next.reportTime = startup.reportTime := by
  obtain ⟨_, ha, rfl⟩ := (silentNext_some_iff accounting startup next action).mp hn
  cases action <;> simp_all [silentAction, silentUpdate, Startup.allocatePublic,
    Startup.executePublic, Startup.advancePublic, Startup.stopPublic]

theorem settle_frames {Seed : Type*} (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed)
    (fuel : ℕ) (seed : Seed) (startup : Startup I) :
    (settle accounting sourceRule fuel seed startup).1.reviews = startup.reviews ∧
      (settle accounting sourceRule fuel seed startup).1.written = startup.written ∧
      (settle accounting sourceRule fuel seed startup).1.writeSerial = startup.writeSerial ∧
      (settle accounting sourceRule fuel seed startup).1.reportTime = startup.reportTime := by
  induction fuel generalizing startup with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ fuel ih =>
    generalize hn : silentNext accounting startup (sourceRule seed startup.history) = next
    cases next with
    | none => simp only [settle, hn, and_self]
    | some next =>
      have hf := silentNext_frames accounting startup next _ hn
      have ht := ih next
      simp only [settle, hn]
      exact ⟨ht.1.trans hf.1, ht.2.1.trans hf.2.1,
        ht.2.2.1.trans hf.2.2.1, ht.2.2.2.trans hf.2.2.2⟩

end PaperProofs.Retained.PRetAdministrativeFrames013
