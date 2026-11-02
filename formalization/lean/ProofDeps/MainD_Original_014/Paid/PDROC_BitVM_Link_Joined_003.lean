module

public import Paid.PDROC_BitVM_Link_Codec_002
public import Common.PSTR_WordBool_SupportClock_007
public import Common.PSTR_SYM_FiniteRelabel_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/- Maximal planned ordinary joint-import CANDIDATE only, NOT compiled.
It intentionally excludes old PaidNeutral003 and every formal PSTR_TM_*
module. The actual new compiler run is deferred until the parent's exact
packet fixes one owner/product path per module. No compatibility verdict
or machine-existence claim follows from this source file. -/

namespace PDROC.BitVM.Link.JoinedCandidate

open PaperProofs.Paid.Computation

#check PDROC.BitVM.Link.CodecCandidate.encodeBits_eq_neutral
#check PaperProofs.Common.Native.PSTRWordBool.SupportClock.actual_native_trace
#check PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRelabel.finiteMachine
#check PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRelabel.finite_runs
#check PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002.encodeDatum_rat_runsFrom
#check PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticUnblock004.marker_originalNat_runsFrom

example {states : ℕ}
    (machine : PaperProofs.Common.Native.RationalControllerComputation.Machine states) : BitMachine states := machine

example {states : ℕ} (machine : BitMachine states) (input : List Bool)
    (trace : List (BitState states)) (final : BitState states) :
    BitRuns machine input trace final ↔
      PaperProofs.Common.Native.RationalControllerComputation.Runs machine input trace final :=
  PDROC.BitVM.Link.CodecCandidate.bitRuns_iff_neutral machine input trace final

end PDROC.BitVM.Link.JoinedCandidate
