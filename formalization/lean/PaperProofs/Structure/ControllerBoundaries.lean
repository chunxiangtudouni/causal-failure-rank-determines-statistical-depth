module

public import PaperProofs.Structure.IndexedQuery
public import PaperProofs.Structure.RestrictedGame

/-!
The boundary statements in frozen laminar-proofs.tex:263--280 use the same
stored tables and exact query as A15. Lists are arbitrary: repeated stages,
tools absent from every listed stage and an initial unavailable-tool set
are not removed from the quantifiers. Deletion preserves laminarity and
has exactly the independent game's remaining-tool semantics.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*} [DecidableEq Tool]

theorem laminarSchedule_delete (full : List (Finset Tool))
    (hlaminar : LaminarSchedule full) (unavailable : Finset Tool) :
    LaminarSchedule (full.map (fun eligible => eligible \ unavailable)) := by
  intro left hleft right hright
  obtain ⟨sourceLeft, hsleft, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨sourceRight, hsright, rfl⟩ := List.mem_map.mp hright
  rcases hlaminar sourceLeft hsleft sourceRight hsright with hd | hsub | hsub
  · left
    apply Finset.disjoint_left.mpr
    intro tool hl hr
    exact Finset.disjoint_left.mp hd (Finset.mem_sdiff.mp hl).1 (Finset.mem_sdiff.mp hr).1
  · exact Or.inr (Or.inl (Finset.sdiff_subset_sdiff_left unavailable hsub))
  · exact Or.inr (Or.inr (Finset.sdiff_subset_sdiff_left unavailable hsub))

theorem errorRank_delete_unavailable [Fintype Tool] (full : List (Finset Tool))
    (unavailable used : Finset Tool) :
    errorRank (full.map (fun eligible => eligible \ unavailable)) (Finset.univ \ used) =
      errorRank full (Finset.univ \ (used ∪ unavailable)) := by
  have hmap : full.map (fun eligible => eligible \ unavailable) =
      full.map (fun eligible => eligible ∩ (Finset.univ \ unavailable)) := by
    apply List.map_congr_left
    intro eligible _
    ext tool
    simp
  rw [hmap, errorRank_restrict]
  congr 1
  ext tool
  simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
  tauto

open IndexedQuery IndexedDescent

/-- This identity covers even a tool absent from ALL listed stage sets:
the preprocessed singleton cache still includes it. -/
theorem cached_tool_not_lost (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (tool : Fin q) :
    (prepareNormalization q full).indexed.decode
      ((IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool) = {tool} :=
  IndexedStaticMetadata.buildPositive_tool_decode q full hq tool

/-- At an actual nonterminal infinite-rank state the concrete A15 query
returns a concrete unused compatible tool with infinite successor rank. -/
theorem stored_query_infinite_tool (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length)
    (htop : errorRank (full.drop stage.val) (Finset.univ \ used) = ⊤) :
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    let answer := query (prepareNormalization q full).indexed
      (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used) (storedPositiveRow q full next)
      (storedStageNode q full hq stage)
    ∃ tool, answer.tool = some tool ∧ tool ∈ full[stage.val] ∧ tool ∉ used ∧
      errorRank (full.drop (stage.val + 1)) ((Finset.univ \ used).erase tool) = ⊤ := by
  dsimp only
  rw [List.drop_eq_getElem_cons stage.isLt] at htop
  have hbad := ((errorRank_cons_eq_top_iff full[stage.val] (full.drop (stage.val + 1))
    (Finset.univ \ used)).mp htop).2
  have hnonempty : full[stage.val] ∩ (Finset.univ \ used) ≠ ∅ := by
    intro he
    have hz := (badChildRank_eq_zero_iff full[stage.val] (full.drop (stage.val + 1))
      (Finset.univ \ used)).mpr he
    exact ENat.zero_ne_top (hz.symm.trans hbad)
  let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
  cases hpick : (query (prepareNormalization q full).indexed
      (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used) (storedPositiveRow q full next)
      (storedStageNode q full hq stage)).tool with
  | none => exact (hnonempty ((stored_query_tool_none_iff q full hq hlaminar used stage).mp hpick)).elim
  | some tool =>
    obtain ⟨heligible, hunused, hchild⟩ := stored_query_tool_spec q full hq hlaminar used stage tool hpick
    exact ⟨tool, rfl, heligible, hunused, hchild.trans hbad⟩

/-- N=0 has only the terminal state, independently of the tool count. -/
theorem emptySchedule_terminal (q : Nat) (used : Finset (Fin q)) :
    (terminalReply q).rank = errorRank ([] : List (Finset (Fin q))) (Finset.univ \ used) := by
  rw [errorRank_terminal]
  rfl

/-- q=0 consumes the direct zero-tool table and EMPTY cache, even for
repeated empty stages; there is no inclusion-tree preprocessing branch. -/
theorem zeroTools_laminar (full : List (Finset (Fin 0))) : LaminarSchedule full := by
  intro left _ right _
  left
  apply Finset.disjoint_left.mpr
  intro tool _ _
  exact Fin.elim0 tool

theorem zeroTools_active (full : List (Finset (Fin 0)))
    (used : Finset (Fin 0)) (stage : Fin full.length) :
    let cache := IndexedTable.emptyCache (Fin 0)
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    let answer := query cache (leafTools cache) (usedCounts cache used) (storedZeroRow full next) none
    answer.rank = 1 ∧ answer.bad = 0 ∧ answer.tool = none ∧
      answer.good = errorRank (full.drop (stage.val + 1)) (Finset.univ \ used) :=
  zeroTool_query full (zeroTools_laminar full) used stage

end PaperProofs.Structure.LaminarTree
