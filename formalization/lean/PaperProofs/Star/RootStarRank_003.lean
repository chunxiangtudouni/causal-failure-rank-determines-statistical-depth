module

public import PaperProofs.Star.RootStarRank_002

@[expose] public section

namespace RootStarRank

open PaperProofs.Common PaperProofs.Structure PaperProofs.Statistics PaperProofs.Star

variable {Tool : Type*} [DecidableEq Tool] [Fintype Tool]

omit [Fintype Tool] [DecidableEq Tool] in
theorem constant_eligibility (stages : List (Finset Tool)) (weight : ℝ) :
    eligibilitySchedule (stages.map (fun eligible => (eligible, weight))) = stages := by
  simp only [eligibilitySchedule, List.map_map]
  change stages.map id = stages
  exact List.map_id _

omit [Fintype Tool] in
theorem constant_coefficient_head (eligible : Finset Tool) (later : List (Finset Tool))
    (weight : ℝ) (remaining : Finset Tool) (hg : errorRank later remaining = ⊤)
    (hf : errorRank (eligible :: later) remaining ≠ ⊤) :
    orderedCoefficient ((eligible :: later).map (fun e => (e, weight))) remaining = weight := by
  change orderedCoefficient ((eligible, weight) :: later.map (fun e => (e, weight))) remaining = _
  apply coefficient_head_of_good_top
  · simpa only [constant_eligibility] using hg
  · simpa only [constant_eligibility] using hf

theorem singleton_universal_coefficient (items : List Tool) (hn : items.Nodup) (hne : items ≠ [])
    (weight : ℝ) :
    orderedCoefficient ((singletons items ++ [Finset.univ]).map (fun e => (e, weight)))
      items.toFinset = weight := by
  cases items with
  | nil => exact (hne rfl).elim
  | cons head rest =>
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hn
    have hg : errorRank (singletons rest ++ [Finset.univ]) (head :: rest).toFinset = ⊤ :=
      singleton_universal_rank_top rest hrest _ (by intro tool ht; simp [ht]) head (by simp) hnot
    have hf : errorRank ({head} :: (singletons rest ++ [Finset.univ])) (head :: rest).toFinset ≠ ⊤ := by
      change errorRank (singletons (head :: rest) ++ [Finset.univ]) (head :: rest).toFinset ≠ ⊤
      rw [singleton_universal_rank_exact _ hn]
      exact ENat.natCast_ne_top _
    exact constant_coefficient_head {head} _ weight _ hg hf

theorem universalFirst_coefficient (P : Parameters) :
    (P.input .universalFirst).orderedCoefficient (starInstance P.tools .universalFirst).tools =
      P.channel.a := by
  have hq : 0 < P.tools := by have := P.tools_ge_two; omega
  change orderedCoefficient (P.input .universalFirst).weightedSchedule (Finset.univ : Finset (Fin P.tools)) = _
  rw [weightedSchedule_constant]
  change orderedCoefficient ((List.ofFn (eligibility P.tools .universalFirst)).map
    (fun e : Finset (Fin P.tools) => (e, P.channel.a))) (Finset.univ : Finset (Fin P.tools)) = _
  have hs := universalFirst_compatibility P.tools
  change List.ofFn (eligibility P.tools .universalFirst) = Finset.univ :: singletons (List.finRange P.tools) at hs
  rw [hs]
  apply constant_coefficient_head
  · exact singleton_rank_top _ (List.nodup_finRange P.tools) _ (by intro tool _; exact Finset.mem_univ tool)
  · have hr : errorRank (Finset.univ :: singletons (List.finRange P.tools))
        (Finset.univ : Finset (Fin P.tools)) = 2 :=
      universal_singletons_rank _ (List.nodup_finRange P.tools) _
        (by intro tool _; exact Finset.mem_univ tool)
        (by intro tool _; exact List.mem_finRange tool)
        ⟨⟨0, hq⟩, Finset.mem_univ _⟩
    rw [hr]
    norm_num

theorem singletonsFirst_coefficient (P : Parameters) :
    (P.input .singletonsFirst).orderedCoefficient (starInstance P.tools .singletonsFirst).tools =
      P.channel.a := by
  have hne : List.finRange P.tools ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp only [List.length_finRange, List.length_nil] at hl
    have := P.tools_ge_two
    omega
  have hu : (List.finRange P.tools).toFinset = Finset.univ := by ext tool; simp
  change orderedCoefficient (P.input .singletonsFirst).weightedSchedule (Finset.univ : Finset (Fin P.tools)) = _
  rw [weightedSchedule_constant]
  change orderedCoefficient ((List.ofFn (eligibility P.tools .singletonsFirst)).map
    (fun e : Finset (Fin P.tools) => (e, P.channel.a))) (Finset.univ : Finset (Fin P.tools)) = _
  have hs := singletonsFirst_compatibility P.tools
  change List.ofFn (eligibility P.tools .singletonsFirst) = singletons (List.finRange P.tools) ++ [Finset.univ] at hs
  rw [hs]
  simpa only [hu] using singleton_universal_coefficient _ (List.nodup_finRange P.tools) hne P.channel.a

theorem orderedRankCoefficientClaims (P : Parameters) : P.OrderedRankCoefficientClaims := by
  have hq : 0 < P.tools := by have := P.tools_ge_two; omega
  exact ⟨universalFirst_rank P.tools hq, universalFirst_coefficient P,
    singletonsFirst_rank P.tools, singletonsFirst_coefficient P⟩

end RootStarRank
