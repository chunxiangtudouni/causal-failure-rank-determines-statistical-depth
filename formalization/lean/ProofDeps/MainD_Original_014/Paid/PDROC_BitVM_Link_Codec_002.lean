module

public import PaperProofs.Paid.ComputationalClaims
public import Structure.PA17_TM_RatArithmetic_Parse_002g
public import Structure.PA17_TM_RatArithmetic_Unblock_004d

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/- Ordinary joint-import CANDIDATE only, NOT compiled. Official CC has
no project TM Trace002 import. Use only the A17 PRIVATE TM cone here.
These local mathematical defeq bridges reuse the old Paid003 identities
without importing Paid003's FORMAL Header/Length/Trace/Codec modules.
They are not a new parser, runtime recoder, or rational VM. -/

namespace PDROC.BitVM.Link.CodecCandidate

open PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

def cellDatum : Cell → PaperProofs.Common.Native.RationalControllerComputation.Datum
  | .natural value => .natural value
  | .rational value => .rational value

theorem encodeNatBits_eq_neutral (value : ℕ) :
    encodeNatBits value = PaperProofs.Common.Native.RationalControllerComputation.encodeNat value := rfl

theorem encodeCellBits_eq_neutral (cell : Cell) :
    encodeCellBits cell = PaperProofs.Common.Native.RationalControllerComputation.encodeDatum (cellDatum cell) := by
  cases cell <;> rfl

theorem encodeBits_eq_neutral (cells : List Cell) :
    encodeBits cells = PaperProofs.Common.Native.RationalControllerComputation.encode (cells.map cellDatum) := by
  simp only [encodeBits, PaperProofs.Common.Native.RationalControllerComputation.encode,
    List.length_map, encodeNatBits_eq_neutral, List.flatMap_map]
  congr 2
  apply congrArg (fun encode : Cell → List Bool => cells.flatMap encode)
  funext cell
  exact encodeCellBits_eq_neutral cell

theorem bitRuns_iff_neutral {states : ℕ} (machine : BitMachine states) (input : List Bool)
    (trace : List (BitState states)) (final : BitState states) :
    BitRuns machine input trace final ↔
      PaperProofs.Common.Native.RationalControllerComputation.Runs machine input trace final := Iff.rfl

theorem visitedBitSpace_eq_neutral {states : ℕ} (machine : BitMachine states) (inputLength : ℕ)
    (trace : List (BitState states)) :
    visitedBitSpace machine inputLength trace =
      PaperProofs.Common.Native.RationalControllerComputation.visitedSpace machine inputLength trace := rfl

#check PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002.encodeNat_stream_runsFrom
#check PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002.encodeDatum_rat_runsFrom
#check PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticUnblock004.marker_originalNat_runsFrom
#check PaperProofs.Common.Native.RationalControllerComputation.PSTRTMTrace002.visitedSpace_le

end PDROC.BitVM.Link.CodecCandidate
