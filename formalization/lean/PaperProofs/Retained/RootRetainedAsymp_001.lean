module

public import PaperProofs.Retained.Controller
public import Mathlib.Data.ENat.Monoid

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootRetainedAsymp

open PaperProofs.Common PaperProofs.Retained

variable {I : Instance}

private theorem enat_le_of_nat_lt_imp {left right : ℕ∞}
    (h : ∀ budget : ℕ, (budget : ℕ∞) < left → (budget : ℕ∞) < right) : left ≤ right := by
  apply le_of_not_gt
  intro hlt
  obtain ⟨budget, hb⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have hleft : (budget : ℕ∞) < left := by
    rw [hb]
    exact hlt
  have hi := h budget hleft
  rw [hb] at hi
  exact (lt_irrefl right) hi

private theorem enat_eq_of_nat_lt_iff {left right : ℕ∞}
    (h : ∀ budget : ℕ, (budget : ℕ∞) < left ↔ (budget : ℕ∞) < right) : left = right :=
  le_antisymm (enat_le_of_nat_lt_imp (fun n => (h n).mp))
    (enat_le_of_nat_lt_imp (fun n => (h n).mpr))

theorem rank_positive (later : List I.Stage) (old : Finset I.Stage) (hm : Matchable I old) :
    0 < errorRank I later old := by
  simpa only [ENat.natCast_zero] using
    (safe_iff_lt_errorRank I later old 0).mp ((safe_zero_iff I later old).mpr hm)

theorem rank_zero_of_unmatchable (later : List I.Stage) (old : Finset I.Stage)
    (hm : ¬ Matchable I old) : errorRank I later old = 0 := by
  apply le_antisymm _ bot_le
  apply (rank_le_nat_iff I later old 0).mpr
  exact fun hs => hm ((safe_zero_iff I later old).mp hs)

theorem rank_antitone_old (later : List I.Stage) (small large : Finset I.Stage)
    (hsub : small ⊆ large) : errorRank I later large ≤ errorRank I later small := by
  apply enat_le_of_nat_lt_imp
  intro budget hsafe
  apply (safe_iff_lt_errorRank I later small budget).mp
  apply (safe_iff_future_sets I later small budget).mpr
  intro proposed hfuture hcard
  exact ((safe_iff_future_sets I later large budget).mp
    ((safe_iff_lt_errorRank I later large budget).mpr hsafe) proposed hfuture hcard).subset
      (Finset.union_subset_union hsub (Finset.Subset.refl proposed))

theorem safe_cons_succ (stage : I.Stage) (later : List I.Stage) (old : Finset I.Stage)
    (hm : Matchable I old) (budget : ℕ) :
    Safe I (stage :: later) old (budget + 1) ↔
      Safe I later old (budget + 1) ∧ Safe I later (insert stage old) budget := by
  constructor
  · intro hs
    constructor
    · intro count hc errors play
      exact hs count hc errors (.correct hm play)
    · intro count hc errors play
      exact hs (count + 1) (Nat.add_le_add_right hc 1) (insert stage errors) (.error hm play)
  · rintro ⟨hg, hb⟩ count hc errors play
    cases play with
    | failed _ _ hbad => exact hbad hm
    | correct _ cont => exact hg _ hc _ cont
    | error _ cont => exact hb _ (Nat.le_of_add_le_add_right hc) _ cont

theorem rank_cons (stage : I.Stage) (later : List I.Stage) (old : Finset I.Stage)
    (hm : Matchable I old) :
    errorRank I (stage :: later) old =
      min (errorRank I later old) (1 + errorRank I later (insert stage old)) := by
  apply enat_eq_of_nat_lt_iff
  intro budget
  cases budget with
  | zero =>
    have hp : (0 : ℕ∞) < 1 + errorRank I later (insert stage old) :=
      lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right bot_le)
    simp only [ENat.natCast_zero, lt_min_iff, rank_positive _ _ hm, hp, and_self]
  | succ budget =>
    have hshift : ((budget + 1 : ℕ) : ℕ∞) < 1 + errorRank I later (insert stage old) ↔
        (budget : ℕ∞) < errorRank I later (insert stage old) := by
      rw [ENat.natCast_add, ENat.natCast_one, add_comm (budget : ℕ∞) 1]
      exact ENat.add_lt_add_iff_left (by simp)
    rw [← safe_iff_lt_errorRank, safe_cons_succ stage later old hm budget,
      lt_min_iff, hshift, ← safe_iff_lt_errorRank, ← safe_iff_lt_errorRank]

theorem rank_suffix_step (stage : I.Stage) (old : Finset I.Stage)
    (hh : Healthy I stage.val old) :
    errorRank I (stagesFrom I stage.val) old =
      min (errorRank I (stagesFrom I (stage.val + 1)) old)
        (1 + errorRank I (stagesFrom I (stage.val + 1)) (insert stage old)) := by
  rw [stagesFrom_cons]
  exact rank_cons stage _ old hh.2.2

theorem rank_bad_le_current (stage : I.Stage) (old : Finset I.Stage)
    (hh : Healthy I stage.val old) :
    errorRank I (stagesFrom I (stage.val + 1)) (insert stage old) ≤
      errorRank I (stagesFrom I stage.val) old := by
  rw [rank_suffix_step stage old hh]
  exact le_min (rank_antitone_old _ old (insert stage old) (Finset.subset_insert stage old))
    (by simpa only [add_comm] using
      (le_add_of_nonneg_right (show (0 : ℕ∞) ≤ 1 from bot_le) :
        errorRank I (stagesFrom I (stage.val + 1)) (insert stage old) ≤
          errorRank I (stagesFrom I (stage.val + 1)) (insert stage old) + 1))

theorem rank_past_end_top (next : ℕ) (old : Finset I.Stage)
    (hn : I.stageCount ≤ next) (hm : Matchable I old) :
    errorRank I (stagesFrom I next) old = ⊤ := by
  have hnils : stagesFrom I next = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro stage hs
    have hnext := (mem_stagesFrom I next stage).mp hs
    exact (Nat.not_lt_of_ge (hn.trans hnext)) stage.isLt
  apply (rank_eq_top_iff I _ old).mpr
  intro budget
  rw [safe_iff_future_sets, hnils]
  intro proposed hsub _
  have he : proposed = ∅ := Finset.subset_empty.mp (by simpa only [List.toFinset_nil] using hsub)
  simpa only [he, Finset.union_empty] using hm

end RootRetainedAsymp
