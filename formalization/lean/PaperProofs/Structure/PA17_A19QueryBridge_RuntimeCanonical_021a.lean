module
public import PaperProofs.Structure.PA17_QuerySelection_010

/-! Pure canonical order bridge. A range scan finds the first original
stored child with slack. Counts and capacities are arbitrary; no positivity,
laminarity, capacity invariant or runtime answer premise is required. -/
@[expose] public section
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeCanonical021
open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem range_find_firstSlackChild {q : Nat} (cache : IndexedNodeCache (Fin q))
    (counts capacity : IndexedCapacity cache) (parent : cache.NodeId) (test : Nat → Bool)
    (hchildren : (cache.children.get parent).toList =
      (List.finRange cache.nodes.size).filter (fun child => decide (cache.parents.get child = some parent)))
    (hTest : ∀ n (hn : n < cache.nodes.size), test n =
      decide (cache.parents.get ⟨n, hn⟩ = some parent ∧ counts.get ⟨n, hn⟩ < capacity.get ⟨n, hn⟩)) :
    (((List.range cache.nodes.size).find? test).map Nat.succ).getD 0 =
      encodedNode cache (IndexedDescent.firstSlackChild cache counts capacity parent) := by
  have hfind : (List.finRange cache.nodes.size).find? (test ∘ Fin.val) =
      IndexedDescent.firstSlackChild cache counts capacity parent := by
    rw [IndexedDescent.firstSlackChild, hchildren, List.find?_filter]
    apply List.find?_congr
    intro child _
    simpa only [Function.comp_apply, decide_eq_true_eq] using hTest child.val child.isLt
  rw [← PA17QuerySelection010.finRange_map_val cache.nodes.size, List.find?_map, hfind]
  cases IndexedDescent.firstSlackChild cache counts capacity parent <;> rfl

theorem prepared_find_firstSlackChild {q : Nat} (full : List (Finset (Fin q)))
    (counts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (parent : (prepareNormalization q full).indexed.NodeId) (test : Nat → Bool)
    (hTest : ∀ n (hn : n < (prepareNormalization q full).indexed.nodes.size), test n =
      decide ((prepareNormalization q full).indexed.parents.get ⟨n, hn⟩ = some parent ∧
        counts.get ⟨n, hn⟩ < capacity.get ⟨n, hn⟩)) :
    (((List.range (prepareNormalization q full).indexed.nodes.size).find? test).map Nat.succ).getD 0 =
      encodedNode (prepareNormalization q full).indexed
        (IndexedDescent.firstSlackChild (prepareNormalization q full).indexed counts capacity parent) := by
  exact range_find_firstSlackChild _ counts capacity parent test
    (PA17QuerySelection010.children_eq_filtered (prepareNormalization q full).order.toArray
      (prepareNormalization q full).parentSupport parent) hTest

theorem prepared_encoded_find_firstSlackChild {q : Nat} (full : List (Finset (Fin q)))
    (counts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (parent : (prepareNormalization q full).indexed.NodeId) :
    (((List.range (prepareNormalization q full).indexed.nodes.size).find? (fun n =>
      decide (∃ hn : n < (prepareNormalization q full).indexed.nodes.size,
        encodedNode (prepareNormalization q full).indexed
          ((prepareNormalization q full).indexed.parents.get ⟨n, hn⟩) = parent.val + 1 ∧
          counts.get ⟨n, hn⟩ < capacity.get ⟨n, hn⟩))).map Nat.succ).getD 0 =
      encodedNode (prepareNormalization q full).indexed
        (IndexedDescent.firstSlackChild (prepareNormalization q full).indexed counts capacity parent) := by
  apply prepared_find_firstSlackChild full counts capacity parent
  intro n hn
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨hn', hp, hs⟩
    exact ⟨(UniformNormalizationRAM.encodedNode_eq_some _ _ parent).mp hp, hs⟩
  · rintro ⟨hp, hs⟩
    exact ⟨hn, (UniformNormalizationRAM.encodedNode_eq_some _ _ parent).mpr hp, hs⟩

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeCanonical021
