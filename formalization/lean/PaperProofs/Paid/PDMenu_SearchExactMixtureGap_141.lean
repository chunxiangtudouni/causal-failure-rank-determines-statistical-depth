module

public import PaperProofs.Paid.PDMenu_SearchExactState_139
public import PaperProofs.Paid.PDMenu_SearchBracketPrices_140

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- The original D20 claim for the actual iterated search, including the
literal initial whole-policy coin and the independent full-policy value. -/
theorem exactMixtureAndGap (P : Parameters) : P.ExactMixtureAndGap := by
  intro fee hfee C accounting steps
  dsimp only
  have hi := multiplierSearch_stateBracketCorrect P fee hfee C accounting steps
  refine ⟨hi, ?_⟩
  cases hs : P.multiplierSearch fee steps with
  | exact solution =>
      simp only [hs] at hi ⊢
      exact searchExact_records P fee hfee C accounting solution hi
  | bracket lower upper =>
      simp only [hs] at hi ⊢
      have hm := searchBracket_mixture_records P fee hfee C accounting lower upper hi
      have hslope := searchBracket_slopeBounds P fee hfee C accounting lower upper hi
      have hg := searchBracket_gapBounds P fee hfee C accounting lower upper hi
      exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2,
        hslope.1, hslope.2, hg.1, hg.2.1, hg.2.2,
        searchBracket_lower_le_value P fee hfee C accounting lower upper hi,
        searchBracket_value_le_mixture P fee hfee C accounting lower upper hi⟩

end PDMenu
