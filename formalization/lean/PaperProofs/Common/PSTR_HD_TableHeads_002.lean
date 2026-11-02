module

public import PaperProofs.Common.PSTR_HD_Heads_001
public import PaperProofs.Structure.PSTR_Callback_001

/-! Original L01 head formula, using the table's actual callback ranks.
This identifies symbols only and does not claim a packed-machine compiler. -/

@[expose] public section

namespace PaperProofs.Common.Native.CompactPrice.PSTRHeads

open PaperProofs.Common.SymbolicPrice PaperProofs.Structure PaperProofs.Structure.LaminarTree

/-- Exact semantic scan: the table tie enters only through its independent bad rank. -/
theorem criticalIndices_eq_rankHeadIndices (q : ℕ) (full : List (Finset (Fin q)))
    (hl : LaminarSchedule full) (used : Finset (Fin q)) :
    criticalIndices q full used =
      if errorRank full (Finset.univ \ used) = ⊤ then []
      else rankHeadIndices full (Finset.univ \ used) (errorRank full (Finset.univ \ used)) 0 := by
  simp only [criticalIndices, PSTRCallback.callback_rank q full hl, List.drop_zero]
  split_ifs with h
  · rfl
  · unfold rankHeadIndices
    simp only [Nat.zero_add]
    apply congrArg (List.map Fin.val)
    apply List.filter_congr
    intro stage _
    rw [(PSTRCallback.callback_stage q full hl stage used).2.1,
      List.getD_eq_getElem full ∅ stage.isLt]

/-- The exact first conjunct of the original SymbolicCompilationClaims.
It keeps original stage indices even for repeated experiments. -/
theorem criticalIndices_inputHeads {I : Instance} (hl : LaminarSchedule I.compatibility)
    (input : StatisticalInput I) (available : Finset I.Tool) :
    criticalIndices I.toolCount I.compatibility (Finset.univ \ available) =
      (inputHeads input available).map Prod.fst := by
  have hremaining : (Finset.univ \ (Finset.univ \ available) : Finset I.Tool) = available := by
    ext tool
    simp
  rw [criticalIndices_eq_rankHeadIndices _ _ hl, hremaining]
  simp only [inputHeads, genericRank_eq_errorRank]
  split_ifs with h
  · rfl
  · rw [heads_fst, compatibility_inputSchedule]

/-- The original symbolic coefficient is preserved at exactly the same input. -/
theorem symbolic_formula {I : Instance} (hl : LaminarSchedule I.compatibility)
    (input : StatisticalInput I) (available : Finset I.Tool) :
    criticalIndices I.toolCount I.compatibility (Finset.univ \ available) =
      (inputHeads input available).map Prod.fst ∧
    (inputExpression input available).eval = input.orderedCoefficient available :=
  ⟨criticalIndices_inputHeads hl input available, inputExpression_eval input available⟩

/-- The finite head scan emits at most one original index per stage. -/
theorem criticalIndices_length_le (q : ℕ) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    (criticalIndices q full used).length ≤ full.length := by
  dsimp only [criticalIndices]
  split
  · exact Nat.zero_le _
  · simp only [List.length_map]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange

theorem criticalIndices_mem_lt (q : ℕ) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    {index : ℕ} (hi : index ∈ criticalIndices q full used) : index < full.length := by
  dsimp only [criticalIndices] at hi
  split at hi
  · exact False.elim (List.not_mem_nil hi)
  · obtain ⟨stage, _, rfl⟩ := List.mem_map.mp hi
    exact stage.isLt

theorem criticalIndices_nodup (q : ℕ) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    (criticalIndices q full used).Nodup := by
  dsimp only [criticalIndices]
  split
  · exact List.nodup_nil
  · exact ((List.nodup_finRange _).filter _).map Fin.val_injective

theorem headWords_length_le (q : ℕ) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    (headWords q full used).length ≤ full.length + 2 := by
  have hh := criticalIndices_length_le q full used
  simp only [headWords, List.length_append, List.length_cons, List.length_nil]
  omega

end PaperProofs.Common.Native.CompactPrice.PSTRHeads


