module

public import PaperProofs.Retained.PRet_InformationPackets_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetSourceResponse009

open Common Common.Native PRetPublicAdministrativeReplay005 PRetInformationPackets006

variable {I : Instance}

/-- A real review response updates the original public cache exactly. The
tape is an argument only of this semantic proof, never of consume/shadow. -/
theorem review_response {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (tapes : ReviewTapes input) (s next : State I) (stage : I.Stage)
    (hselected : rule seed s.history = .review stage)
    (hstep : Step input C mode accounting tapes s (.review stage) next) :
    consume accounting rule seed (publicStartup s)
      (.review stage (tapes stage (s.ledger.reviews stage).toNat).val) =
      some (settle accounting rule (I.stageCount + 2 * I.toolCount + 2) seed (publicStartup next)).1 := by
  have ha := step_source_active input C mode accounting tapes hstep
  have hcondition : (publicStartup s).halted = false ∧
      rule seed (publicStartup s).history =
        (Packet.review stage (tapes stage (s.ledger.reviews stage).toNat).val).action := ⟨ha, hselected⟩
  rw [consume, ite_eq_left hcondition]
  cases hstep
  rw [Packet.applyPublic, ← publicStartup_review]

/-- The source early report is supplied only as its actual response. Its
serial is generated from the original source clock by writePublic. -/
theorem write_response {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (tapes : ReviewTapes input)
    (s next : State I) (stage : I.Stage) (bit : Bool)
    (hselected : rule seed s.history = .write stage bit)
    (hstep : Step input C mode accounting tapes s (.write stage bit) next) :
    consume accounting rule seed (publicStartup s) (.write stage bit (s.ledger.truth stage)) =
      some (settle accounting rule (I.stageCount + 2 * I.toolCount + 2) seed (publicStartup next)).1 := by
  have ha := step_source_active input C mode accounting tapes hstep
  have hcondition : (publicStartup s).halted = false ∧
      rule seed (publicStartup s).history = (Packet.write stage bit (s.ledger.truth stage)).action := ⟨ha, hselected⟩
  rw [consume, ite_eq_left hcondition]
  cases hstep
  rw [Packet.applyPublic, ← publicStartup_write_early C hearly]

end PaperProofs.Retained.PRetSourceResponse009
