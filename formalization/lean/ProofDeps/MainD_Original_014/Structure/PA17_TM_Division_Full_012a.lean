module
public import Structure.PA17_TM_Division_Front_007a
public import Structure.PA17_TM_Division_Loop_002h
public import Structure.PA17_TM_Division_Codec_003h

/-! The two fixed original-input programs share the SAME physical long-
division kernel. All code and state counts precede every original a,b. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionFull012

/-- Real raw-pair transport followed by the fixed seventeen-phase kernel. -/
def commonMachine : Machine 995 :=
  PSTRTMSeq005.seqMachine PA17TMDivisionFront007.frontMachine PA17TMDivisionLoop002.loopMachine

/-- Fixed1137 labels: the shared computation, then real quotient cleanup. -/
def quotientMachine : Machine 1136 :=
  PSTRTMSeq005.seqMachine commonMachine PA17TMDivisionCodec003.quotientTailMachine

/-- Fixed1114 labels: the shared computation, then real remainder cleanup. -/
def remainderMachine : Machine 1113 :=
  PSTRTMSeq005.seqMachine commonMachine PA17TMDivisionCodec003.remainderTailMachine

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionFull012
