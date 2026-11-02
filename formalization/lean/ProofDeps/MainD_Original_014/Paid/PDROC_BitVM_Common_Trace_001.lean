module

public import Paid.PDROC_BitVM_Link_Joined_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Common

open PaperProofs.Paid.Computation
open PaperProofs.Common.Native.RationalControllerComputation

/-- The original eval clause follows from the SAME genuine transition
chain and real HALT. No source trace is selected or supplied at runtime. -/
theorem bitRuns_of_chain {states : ℕ} (machine : BitMachine states) (input : List Bool)
    (trace : List (BitState states)) (final : BitState states)
    (first : trace.head? = some (Turing.TM0.init input))
    (chain : trace.IsChain (fun before after => Turing.TM0.step machine before = some after))
    (last : trace.getLast? = some final) (halt : Turing.TM0.step machine final = none) :
    BitRuns machine input trace final :=
  (Link.CodecCandidate.bitRuns_iff_neutral machine input trace final).mpr
    (PSTRTMTrace002.runs_of_chain machine input trace final first chain last halt)

/-- Original visited-bit space on the original actual trace. Unit head
displacements suffice; no separate space qualification is required. -/
theorem visitedBitSpace_le {states : ℕ} (machine : BitMachine states) (inputLength : ℕ)
    (trace : List (BitState states)) :
    visitedBitSpace machine inputLength trace ≤ inputLength + 2 * trace.length + 1 := by
  rw [Link.CodecCandidate.visitedBitSpace_eq_neutral]
  exact PSTRTMTrace002.visitedSpace_le machine inputLength trace

theorem visitedBitSpace_of_clock {states : ℕ} (machine : BitMachine states) (inputLength : ℕ)
    (trace : List (BitState states)) (clock : ℕ) (bounded : trace.length ≤ clock) :
    visitedBitSpace machine inputLength trace ≤ inputLength + 2 * clock + 1 :=
  (visitedBitSpace_le machine inputLength trace).trans (by omega)

end PDROC.BitVM.Common
