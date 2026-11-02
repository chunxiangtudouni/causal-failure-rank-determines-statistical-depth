module

public import PaperProofs.Retained.Controller

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootRetainedQueries

open PaperProofs.Common PaperProofs.Retained

theorem unsafeBudget_iff (I : Instance) (next : ℕ) (old : Finset I.Stage) (budget : ℕ) :
    unsafeBudget I next old budget = true ↔
      errorRank I (stagesFrom I next) old ≤ (budget : ℕ∞) := by
  simp only [unsafeBudget, decide_eq_true_eq, rank_le_nat_iff_future_set,
    Finset.mem_powerset]

theorem finite_rank_bound (I : Instance) (next : ℕ) (old : Finset I.Stage) (depth : ℕ)
    (h : errorRank I (stagesFrom I next) old = (depth : ℕ∞)) : depth ≤ I.stageCount := by
  obtain ⟨future, _, _, hbad⟩ :=
    (rank_le_nat_iff_future_set I (stagesFrom I next) old depth).mp h.le
  have hcard : future.card ≤ I.stageCount := by
    simpa only [Fintype.card_fin, Instance.stageCount] using future.card_le_univ
  have hle := (rank_le_nat_iff_future_set I (stagesFrom I next) old I.stageCount).mpr
    ⟨future, by assumption, hcard, hbad⟩
  rw [h] at hle
  exact ENat.natCast_le_natCast.mp hle

theorem find_range_iff (p : ℕ → Bool) (bound depth : ℕ) :
    (List.range bound).find? p = some depth ↔
      p depth = true ∧ depth < bound ∧ ∀ smaller < depth, p smaller = false := by
  simp only [List.find?_eq_some_iff_getElem, List.length_range, List.getElem_range]
  constructor
  · rintro ⟨hp, i, hi, rfl, hs⟩
    exact ⟨hp, hi, by simpa using hs⟩
  · rintro ⟨hp, hd, hs⟩
    exact ⟨hp, depth, hd, rfl, by simpa using hs⟩

theorem rankQueryCorrect (I : Instance) : RankQueryCorrect I := by
  classical
  intro next old
  constructor
  · constructor
    · intro hnone
      apply (rank_eq_top_iff I (stagesFrom I next) old).mpr
      intro budget
      by_contra hbad
      obtain ⟨future, hsub, _, hbad⟩ :=
        (not_safe_iff_future_set I (stagesFrom I next) old budget).mp hbad
      have hcard : future.card ≤ I.stageCount := by
        simpa only [Fintype.card_fin, Instance.stageCount] using future.card_le_univ
      have hunsafe : unsafeBudget I next old future.card = true :=
        (unsafeBudget_iff I next old future.card).mpr
          ((rank_le_nat_iff_future_set I (stagesFrom I next) old future.card).mpr
            ⟨future, hsub, le_rfl, hbad⟩)
      have hn := List.find?_eq_none.mp hnone future.card (List.mem_range.mpr (by omega))
      exact hn hunsafe
    · intro htop
      apply List.find?_eq_none.mpr
      intro depth _ hd
      have hle := (unsafeBudget_iff I next old depth).mp hd
      rw [htop] at hle
      exact ENat.natCast_ne_top depth (top_le_iff.mp hle)
  · intro depth
    rw [rankIndex, find_range_iff]
    constructor
    · rintro ⟨hd, _, hsmall⟩
      apply (rank_eq_nat_iff I (stagesFrom I next) old depth).mpr
      refine ⟨(rank_le_nat_iff I (stagesFrom I next) old depth).mp
        ((unsafeBudget_iff I next old depth).mp hd), ?_⟩
      intro smaller hs
      by_contra hbad
      have ht := (unsafeBudget_iff I next old smaller).mpr
        ((rank_le_nat_iff I (stagesFrom I next) old smaller).mpr hbad)
      simp only [hsmall smaller hs, Bool.false_eq_true] at ht
    · intro h
      refine ⟨(unsafeBudget_iff I next old depth).mpr h.le,
        by have := finite_rank_bound I next old depth h; omega, ?_⟩
      intro smaller hs
      apply Bool.eq_false_iff.mpr
      intro ht
      have hsafe := ((rank_eq_nat_iff I (stagesFrom I next) old depth).mp h).2 smaller hs
      exact ((rank_le_nat_iff I (stagesFrom I next) old smaller).mp
        ((unsafeBudget_iff I next old smaller).mp ht)) hsafe

end RootRetainedQueries
