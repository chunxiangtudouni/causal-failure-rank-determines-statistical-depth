module

public import PaperProofs.Common.ReferenceSharpNativeUpper

/-! Conditional assembly of the original full fixed-graph price package.
Only its still-pending independent native lower half remains an assumption.
The actual qualified native upper and infinite-rank witness are proved. -/

@[expose] public section

namespace PaperProofs.Common

open PaperProofs.Structure Native

variable {I : Instance}

theorem StatisticalInput.fixedGraphPriceLaw_of_nativeLower (input : StatisticalInput I)
    (hlower : input.NativeLowerPriceLaw) : input.FixedGraphPriceLaw := by
  refine ⟨hlower, input.nativeUpperPriceLaw, input.nativeInfiniteRankPriceLaw, ?_⟩
  intro depth hrank
  apply input.orderedCoefficient_pos
  rw [hrank]
  exact ENat.natCast_ne_top depth

end PaperProofs.Common
