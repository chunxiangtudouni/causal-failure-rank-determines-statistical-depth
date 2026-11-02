module

public import PaperProofs.Paid.PDROC_Simulator_029
public import PaperProofs.Paid.PDROC_SimulatorProjection_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- A matching shadow history transports the protocol's public phase fields
between two genuine Prefixes. Neither Prefix is replaced by a new guard. -/
theorem simulator_prefix_state_projection {ActualSeed VirtualSeed SimSeed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I)
    (actual : PolicyRule I ActualSeed) (actualSeed : ActualSeed)
    (actualTruth : I.Stage → Bool) (actualTapes : ReviewTapes input)
    {an : ℕ} {a : State I}
    (ap : Prefix input C mode accounting actual actualSeed actualTruth actualTapes an a)
    (virtual : PolicyRule I VirtualSeed) (virtualSeed : VirtualSeed)
    (virtualTruth : I.Stage → Bool) (virtualTapes : ReviewTapes input)
    {vn : ℕ} {v : State I}
    (vp : Prefix input C mode accounting virtual virtualSeed virtualTruth virtualTapes vn v)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I)) (seed : SimSeed)
    (hh : (simulatorReplay draw seed a.history).shadow = v.history) :
    a.cursor = v.cursor ∧ a.halted = v.halted ∧
      ∀ stage, a.ledger.written stage = none ↔ v.ledger.written stage = none := by
  have hproj := simulatorReplay_sameProjection draw seed a.history
  refine ⟨?_, ?_, ?_⟩
  · exact (prefix_historyCursor input C mode accounting actual actualSeed actualTruth actualTapes ap).symm.trans
      (hproj.1.trans ((congrArg historyCursor hh).trans
        (prefix_historyCursor input C mode accounting virtual virtualSeed virtualTruth virtualTapes vp)))
  · exact (prefix_historyHalted input C mode accounting actual actualSeed actualTruth actualTapes ap).symm.trans
      (hproj.2.2.2.2.trans ((congrArg historyHalted hh).trans
        (prefix_historyHalted input C mode accounting virtual virtualSeed virtualTruth virtualTapes vp)))
  · intro stage
    rw [← prefix_historyWritten input C mode accounting actual actualSeed actualTruth actualTapes ap stage,
      ← prefix_historyWritten input C mode accounting virtual virtualSeed virtualTruth virtualTapes vp stage,
      ← hh]
    exact hproj.2.2.2.1 stage

end PDROC
