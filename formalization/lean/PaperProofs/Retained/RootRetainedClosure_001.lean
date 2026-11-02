module

public import PaperProofs.Retained.PRet_FreshRecursion_115
public import PaperProofs.Retained.RootRetainedAsymp_003
public import PaperProofs.Retained.RootRetainedHead_004
public import PaperProofs.Retained.RootRetainedQueries_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.RootRetainedClosure

open Common

theorem freshPenaltyRecursion {I : Instance} (input : StatisticalInput I) :
    FreshPenaltyRecursion input := PRetFreshRecursion115.freshPenaltyRecursion input

theorem freshPenaltyAsymptotics {I : Instance} (input : StatisticalInput I) :
    FreshPenaltyAsymptotics input :=
  (RootRetainedAsymp.freshAsymptotics_of_recursion input (freshPenaltyRecursion input)).1

theorem equalRankCancellation {I : Instance} (input : StatisticalInput I) :
    EqualRankCancellation input :=
  (RootRetainedAsymp.freshAsymptotics_of_recursion input (freshPenaltyRecursion input)).2

theorem nativeLowerPriceLaw {I : Instance} (input : StatisticalInput I) :
    NativeLowerPriceLaw input :=
  RootRetainedHead.nativeLowerPriceLaw_of_recursion input (freshPenaltyRecursion input)

theorem rankQueryCorrect (I : Instance) : RankQueryCorrect I :=
  RootRetainedQueries.rankQueryCorrect I

theorem terminalAssignmentCorrect (I : Instance) : TerminalAssignmentCorrect I :=
  RootRetainedQueries.terminalAssignmentCorrect I

end PaperProofs.Retained.RootRetainedClosure
