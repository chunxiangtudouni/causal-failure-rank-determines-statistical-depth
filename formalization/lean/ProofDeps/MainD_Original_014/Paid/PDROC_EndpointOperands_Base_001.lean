module

public import Paid.RootD27Endpoint_CalleeSpace_036
public import Paid.PDROC_CalibrationRow_OperandPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDROC.EndpointOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDCompute.Solver RootD27.Endpoint RootD27.Bits

/-- A fixed cap for NEW assigned naturals. Old caller cells retain their
actual caller budget; this definition imposes no bound on old scratch. -/
def naturalCap (P : Parameters) (base E returnPC : ℕ) : ℕ :=
  base+E+returnPC+2*P.certificate.M+256

def pcCap (origin returnPC : ℕ) : ℕ := origin+returnPC+512

structure ControlBudget (P : Parameters) (origin base E returnPC budget : ℕ) : Prop where
  small : 8≤budget
  naturalBits : 1+natBits (naturalCap P base E returnPC)≤budget
  pcBits : natBits (pcCap origin returnPC)≤budget

theorem ControlBudget.nat (P : Parameters) (origin base E returnPC budget n : ℕ)
    (bounds : ControlBudget P origin base E returnPC budget)
    (inside : n≤naturalCap P base E returnPC) : (Cell.natural n).bits≤budget :=
  (Nat.add_le_add_left (natBits_mono inside) 1).trans bounds.naturalBits

theorem ControlBudget.address (P : Parameters) (origin base E returnPC budget n : ℕ)
    (bounds : ControlBudget P origin base E returnPC budget)
    (inside : n≤naturalCap P base E returnPC) : 1+natBits n≤budget :=
  ControlBudget.nat P origin base E returnPC budget n bounds inside

theorem ControlBudget.pc (P : Parameters) (origin base E returnPC budget counter : ℕ)
    (bounds : ControlBudget P origin base E returnPC budget)
    (inside : counter≤pcCap origin returnPC) : natBits counter≤budget :=
  (natBits_mono inside).trans bounds.pcBits

theorem ControlBudget.headerAddress (P : Parameters) (origin base E returnPC budget : ℕ)
    (bounds : ControlBudget P origin base E returnPC budget) :
    1+natBits (base+headerWords)≤budget := by
  apply ControlBudget.address P origin base E returnPC budget _ bounds
  unfold naturalCap headerWords
  omega

theorem ControlBudget.zeroRat (P : Parameters) (origin base E returnPC budget : ℕ)
    (bounds : ControlBudget P origin base E returnPC budget) :
    (Cell.rational 0).bits≤budget :=
  (show (Cell.rational 0).bits≤8 by decide).trans bounds.small

theorem safeBits_mono {state : State} {smaller larger : ℕ}
    (safe : SafeBits state smaller) (bound : smaller≤larger) : SafeBits state larger :=
  fun bits member => (safe bits member).trans bound

end PDROC.EndpointOperands
