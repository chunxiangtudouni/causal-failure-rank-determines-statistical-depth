module

public import PaperProofs.Star.Model

@[expose] public section

namespace RootStarRank

open PaperProofs.Common PaperProofs.Structure

variable {Tool : Type*} [DecidableEq Tool]

def singletons (items : List Tool) : List (Finset Tool) := items.map (fun tool => {tool})

theorem bad_singleton (tool : Tool) (later : List (Finset Tool)) (remaining : Finset Tool)
    (hm : tool ∈ remaining) :
    badChildRank {tool} later remaining = errorRank later (remaining.erase tool) := by
  have hi : ({tool} : Finset Tool) ∩ remaining = {tool} := by ext x; simp [hm]
  simp only [badChildRank, hi, Finset.sup_singleton]

theorem singleton_rank_top (items : List Tool) (hn : items.Nodup) (remaining : Finset Tool)
    (hc : ∀ tool ∈ items, tool ∈ remaining) : errorRank (singletons items) remaining = ⊤ := by
  induction items generalizing remaining with
  | nil => exact errorRank_terminal _
  | cons head rest ih =>
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hn
    have hh : head ∈ remaining := hc head (List.mem_cons_self)
    have hgood := ih hrest remaining (fun tool h => hc tool (List.mem_cons_of_mem _ h))
    have hbad := ih hrest (remaining.erase head) (by
      intro tool ht
      refine Finset.mem_erase.mpr ⟨?_, hc tool (List.mem_cons_of_mem _ ht)⟩
      intro he
      exact hnot (he ▸ ht))
    change errorRank ({head} :: singletons rest) remaining = ⊤
    rw [errorRank_cons, hgood, bad_singleton head _ _ hh, hbad]
    simp

theorem not_safe_singletons_missing (items : List Tool) (remaining : Finset Tool)
    (hm : ∃ tool ∈ items, tool ∉ remaining) : ¬ Safe (singletons items) remaining 1 := by
  induction items with
  | nil => obtain ⟨tool, ht, _⟩ := hm; cases ht
  | cons head rest ih =>
    intro hs
    obtain ⟨hgood, chosen, hchosen, _⟩ := (safe_cons_succ_iff {head} (singletons rest) remaining 0).mp hs
    obtain ⟨tool, hmem, hnot⟩ := hm
    rcases List.mem_cons.mp hmem with he | ht
    · subst tool
      have heq : chosen = head := Finset.mem_singleton.mp (Finset.mem_inter.mp hchosen).1
      exact hnot (heq ▸ (Finset.mem_inter.mp hchosen).2)
    · exact ih ⟨tool, ht, hnot⟩ hgood

theorem singleton_rank_one_missing (items : List Tool) (remaining : Finset Tool)
    (hm : ∃ tool ∈ items, tool ∉ remaining) : errorRank (singletons items) remaining = 1 :=
  errorRank_eq_one_of_not_safe_one _ _ (not_safe_singletons_missing items remaining hm)

variable [Fintype Tool]

theorem universal_rank_top (remaining : Finset Tool) (h : remaining.Nonempty) :
    errorRank [Finset.univ] remaining = ⊤ := by
  obtain ⟨tool, hm⟩ := h
  have hb : badChildRank Finset.univ [] remaining = ⊤ := by
    apply top_le_iff.mp
    simpa only [errorRank_terminal] using
      (childRank_le_badChildRank Finset.univ [] remaining (Finset.mem_inter.mpr ⟨Finset.mem_univ tool, hm⟩))
  exact (errorRank_cons_eq_top_iff _ _ _).mpr ⟨errorRank_terminal _, hb⟩

theorem singleton_universal_rank_top (items : List Tool) (hn : items.Nodup) (remaining : Finset Tool)
    (hc : ∀ tool ∈ items, tool ∈ remaining) (spare : Tool) (hspare : spare ∈ remaining) (hnot : spare ∉ items) :
    errorRank (singletons items ++ [Finset.univ]) remaining = ⊤ := by
  induction items generalizing remaining with
  | nil => exact universal_rank_top remaining ⟨spare, hspare⟩
  | cons head rest ih =>
    obtain ⟨hhead, hrest⟩ := List.nodup_cons.mp hn
    have hh : head ∈ remaining := hc head (List.mem_cons_self)
    have htail : spare ∉ rest := fun h => hnot (List.mem_cons_of_mem _ h)
    have hgood := ih hrest remaining (fun tool ht => hc tool (List.mem_cons_of_mem _ ht)) hspare htail
    have hbad := ih hrest (remaining.erase head) (by
      intro tool ht
      refine Finset.mem_erase.mpr ⟨?_, hc tool (List.mem_cons_of_mem _ ht)⟩
      intro he; exact hhead (he ▸ ht))
      (Finset.mem_erase.mpr ⟨fun he => hnot (List.mem_cons.mpr (Or.inl he)), hspare⟩) htail
    change errorRank ({head} :: (singletons rest ++ [Finset.univ])) remaining = ⊤
    exact (errorRank_cons_eq_top_iff _ _ _).mpr ⟨hgood, (bad_singleton head _ _ hh).trans hbad⟩

theorem singleton_universal_rank_exact (items : List Tool) (hn : items.Nodup) :
    errorRank (singletons items ++ [Finset.univ]) items.toFinset = (items.length + 1 : ℕ) := by
  induction items with
  | nil => exact errorRank_no_tools Finset.univ []
  | cons head rest ih =>
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hn
    have he : (head :: rest).toFinset.erase head = rest.toFinset := by simp [hnot]
    have hgood : errorRank (singletons rest ++ [Finset.univ]) (head :: rest).toFinset = ⊤ :=
      singleton_universal_rank_top rest hrest _ (by intro tool ht; simp [ht]) head (by simp) hnot
    have hh : head ∈ (head :: rest).toFinset := by simp
    change errorRank ({head} :: (singletons rest ++ [Finset.univ])) (head :: rest).toFinset = _
    rw [errorRank_cons, hgood, bad_singleton head _ _ hh, he, ih hrest]
    norm_num [add_comm, add_left_comm]

end RootStarRank
