module

public import PaperProofs.Star.RootStarRank_001

@[expose] public section

namespace RootStarRank

open PaperProofs.Common PaperProofs.Structure PaperProofs.Statistics PaperProofs.Star

variable {Tool : Type*} [DecidableEq Tool] [Fintype Tool]

theorem universal_singletons_bad (items : List Tool) (remaining : Finset Tool)
    (hc : ∀ tool ∈ remaining, tool ∈ items) (hne : remaining.Nonempty) :
    badChildRank Finset.univ (singletons items) remaining = 1 := by
  have each (tool : Tool) (hm : tool ∈ remaining) :
      errorRank (singletons items) (remaining.erase tool) = 1 :=
    singleton_rank_one_missing items _ ⟨tool, hc tool hm, by simp⟩
  apply le_antisymm
  · apply Finset.sup_le
    intro tool ht
    rw [each tool (Finset.mem_inter.mp ht).2]
  · obtain ⟨tool, ht⟩ := hne
    simpa only [each tool ht] using
      (childRank_le_badChildRank Finset.univ (singletons items) remaining
        (Finset.mem_inter.mpr ⟨Finset.mem_univ tool, ht⟩))

theorem universal_singletons_rank (items : List Tool) (hn : items.Nodup) (remaining : Finset Tool)
    (hc : ∀ tool ∈ items, tool ∈ remaining) (hr : ∀ tool ∈ remaining, tool ∈ items)
    (hne : remaining.Nonempty) :
    errorRank (Finset.univ :: singletons items) remaining = 2 := by
  rw [errorRank_cons, singleton_rank_top items hn remaining hc,
    universal_singletons_bad items remaining hr hne]
  norm_num

omit [Fintype Tool] in
theorem coefficient_head_of_good_top (eligible : Finset Tool) (weight : ℝ)
    (later : WeightedSchedule Tool) (remaining : Finset Tool)
    (hg : errorRank (eligibilitySchedule later) remaining = ⊤)
    (hf : errorRank (eligible :: eligibilitySchedule later) remaining ≠ ⊤) :
    orderedCoefficient ((eligible, weight) :: later) remaining = weight := by
  have hb : badChildRank eligible (eligibilitySchedule later) remaining + 1 =
      errorRank (eligible :: eligibilitySchedule later) remaining := by
    rw [errorRank_cons, hg]
    simp [add_comm]
  have hn : ¬ errorRank (eligibilitySchedule later) remaining =
      errorRank (eligible :: eligibilitySchedule later) remaining := by
    rw [hg]
    exact fun h => hf h.symm
  simp [orderedCoefficient, hf, hn, hb]

theorem universalFirst_compatibility (q : ℕ) :
    (starInstance q .universalFirst).compatibility =
      Finset.univ :: singletons (List.finRange q) := by
  change List.ofFn (eligibility q .universalFirst) = Finset.univ :: singletons (List.finRange q)
  rw [List.ofFn_succ]
  have ht : (fun i : Fin q => eligibility q .universalFirst i.succ) = fun i => {i} := by
    funext i
    simp [eligibility, label, Fin.val_succ]
  rw [ht]
  simp [eligibility, label, singletons, ← List.ofFn_id, List.map_ofFn]

theorem singletonsFirst_compatibility (q : ℕ) :
    (starInstance q .singletonsFirst).compatibility =
      singletons (List.finRange q) ++ [Finset.univ] := by
  change List.ofFn (eligibility q .singletonsFirst) = singletons (List.finRange q) ++ [Finset.univ]
  rw [List.ofFn_succ_last]
  have ht : (fun i : Fin q => eligibility q .singletonsFirst i.castSucc) = fun i => {i} := by
    funext i
    simp [eligibility, label, Fin.val_castSucc, i.isLt]
  rw [ht]
  simp [eligibility, label, singletons, ← List.ofFn_id, List.map_ofFn]

theorem universalFirst_rank (q : ℕ) (hq : 0 < q) :
    initialRank (starInstance q .universalFirst) = 2 := by
  change errorRank (starInstance q .universalFirst).compatibility Finset.univ = _
  rw [universalFirst_compatibility]
  exact universal_singletons_rank _ (List.nodup_finRange q) _
    (by intro tool _; exact Finset.mem_univ tool)
    (by intro tool _; exact List.mem_finRange tool)
    ⟨⟨0, hq⟩, Finset.mem_univ _⟩

theorem singletonsFirst_rank (q : ℕ) :
    initialRank (starInstance q .singletonsFirst) = (q + 1 : ℕ) := by
  have hu : (List.finRange q).toFinset = Finset.univ := by ext tool; simp
  change errorRank (List.ofFn (eligibility q .singletonsFirst)) (Finset.univ : Finset (Fin q)) = _
  have hs := singletonsFirst_compatibility q
  change List.ofFn (eligibility q .singletonsFirst) = singletons (List.finRange q) ++ [Finset.univ] at hs
  rw [hs]
  simpa only [hu, List.length_finRange] using singleton_universal_rank_exact _ (List.nodup_finRange q)

theorem weightedSchedule_constant (P : Parameters) (order : Order) :
    (P.input order).weightedSchedule =
      (starInstance P.tools order).compatibility.map (fun eligible => (eligible, P.channel.a)) := by
  conv_rhs => rw [← List.ofFn_get (starInstance P.tools order).compatibility]
  rw [List.map_ofFn]
  unfold StatisticalInput.weightedSchedule
  congr 1
  funext i
  exact Prod.ext rfl (P.local_coefficient_eq order i)

end RootStarRank
