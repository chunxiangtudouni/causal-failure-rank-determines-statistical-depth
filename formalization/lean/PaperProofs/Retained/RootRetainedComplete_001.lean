module

public import PaperProofs.Retained.RootRetainedInfinite_003
public import PaperProofs.Retained.PRet_NativeRearrangement_038
public import PaperProofs.Retained.PRet_FullHistoryBridge_068
public import PaperProofs.Retained.PRet_FreshInfiniteBoundary_044
public import PaperProofs.Retained.RootRetainedClosure_001
public import PaperProofs.Retained.PRet_Alignment_Actual_005
public import PaperProofs.Retained.PRet_Completion_Original_006
public import PaperProofs.Retained.PRet_CompleteUpper_124
public import PaperProofs.Retained.PRet_Overflow_Original_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootRetainedComplete

open PaperProofs.Common PaperProofs.Retained

universe u

/-- All thirteen original retained fields, including all private-seed
universes in rearrangement/full-history comparison and the actual native
finite/infinite-girth policies. Every former interface premise is internal. -/
theorem retainedPriceClaims {I : Instance} (input : StatisticalInput I) : RetainedPriceClaims.{u} input :=
  ⟨PRetNativeRearrangement038.native_rearrangement input,
    PRetFullHistoryBridge068.fullHistoryPenaltyBridge input,
    RootRetainedClosure.freshPenaltyRecursion input,
    PRetFreshInfiniteBoundary044.freshPenaltyBoundaryClaims input,
    RootRetainedClosure.freshPenaltyAsymptotics input,
    RootRetainedClosure.equalRankCancellation input,
    PRetAlignment.referenceAlignment input,
    PRetCompletion.terminalScriptCompletion input,
    PRetReferenceCost123.referenceRiskAndCost input,
    PRetOverflow.truncationAndNativeImplementation input,
    RootRetainedClosure.nativeLowerPriceLaw input,
    PRetCompleteUpper124.nativeUpperPriceLaw input,
    RootRetainedInfinite.nativeInfiniteGirthLaw input⟩

theorem fullRetainedClaims {I : Instance} (input : StatisticalInput I) :
    RetainedPriceClaims.{u} input ∧ RankQueryCorrect I ∧ TerminalAssignmentCorrect I :=
  ⟨retainedPriceClaims input, RootRetainedClosure.rankQueryCorrect I,
    RootRetainedClosure.terminalAssignmentCorrect I⟩

end RootRetainedComplete
