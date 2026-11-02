module

public import Paid.PDROC_D27Prepare_Search_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation

namespace PDROC.D27Prepare.Q

/-- Exact typed boundary after the three original searches, before page10.
There is no premise on heap9. Physical prefix bounds are a separate input
to the actual Q-phase theorem, so this boundary has no resource dependency. -/
structure QInitial (P : Parameters) (fee : ℚ) (state : State) : Prop where
  raw : Search.RawConstants P fee state
  location : state.pc = Program.pc 10
  t0 : Search.SlotHas state 6 (.natural P.certificate.t0)
  M : Search.SlotHas state 7 (.natural P.certificate.M)
  E : Search.SlotHas state 8 (.natural P.certificate.E)
  ratStages : Search.SlotHas state 22 (.rational P.certificate.stages)
  ratT0 : Search.SlotHas state 23 (.rational P.certificate.t0)
  gammaSquared : Search.SlotHas state 24 (.rational (P.certificate.gamma ^ 2))
  variance : Search.SlotHas state 25 (.rational P.certificate.varianceBase)
  varianceSquared : Search.SlotHas state 26 (.rational (P.certificate.varianceBase ^ 2))
  majorityThreshold : Search.SlotHas state 27
    (.rational ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2))
  menuRatio : Search.SlotHas state 29 (.rational P.certificate.menuRatio)
  odds : Search.SlotHas state 30 (.rational P.certificate.odds)
  exponentThreshold : Search.SlotHas state 31 (.rational (P.certificate.gamma * P.certificate.epsilon))

def region : Finset ℕ := {9, 32, 52, 53}

end PDROC.D27Prepare.Q
