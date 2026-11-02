module

public import Structure.PA17_QueryMetadata_010
public import Structure.PA17_LeafLabels_005

/-! Run the existing actual leaf-label pass on queryROM as well as on the
given-tree ROM. Every query may start from arbitrary scratch words. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryLeafLabels012

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17LeafLabels005

theorem prepared_bits_total (q : Nat) (full : List (Finset (Fin q))) (stage : Nat)
    (used : Finset (Fin q)) (node : (prepareNormalization q full).indexed.NodeId) (state : State) :
    (execute (queryROM q full stage used).semantic
      ((List.range q).flatMap (bitBlock full.length q node.val)) state).register .total =
      state.register .total + ((prepareNormalization q full).indexed.decode node).card := by
  rw [bits_total]
  exact congrArg (state.register .total + ·) (PA17QueryMetadata010.rowSum_eq_card q full stage used node)

theorem prepared_bits_value_singleton (q : Nat) (full : List (Finset (Fin q))) (stage : Nat)
    (used : Finset (Fin q)) (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (hsingle : (prepareNormalization q full).indexed.decode node = {tool}) (state : State) :
    (execute (queryROM q full stage used).semantic
      ((List.range q).flatMap (bitBlock full.length q node.val)) state).register .value = tool.val + 1 := by
  apply bits_value_some _ _ _ _ _ tool.val (List.mem_range.mpr tool.isLt)
  · change (queryROM q full stage used).semantic.read .input _ ≠ 0
    rw [PA17QueryCounts008.queryROM_node_bit q full stage used node tool, hsingle]
    simp [bit]
  · intro other ho hne
    have hother : other < q := List.mem_range.mp ho
    have hn : (⟨other, hother⟩ : Fin q) ∈ (prepareNormalization q full).indexed.decode node := by
      by_contra hn
      apply hne
      change (queryROM q full stage used).semantic.read .input _ = 0
      rw [PA17QueryCounts008.queryROM_node_bit q full stage used node ⟨other, hother⟩]
      simp [bit, hn]
    rw [hsingle, Finset.mem_singleton] at hn
    exact congrArg Fin.val hn

theorem prepared_nodeBlock_result (q : Nat) (full : List (Finset (Fin q))) (stage : Nat)
    (used : Finset (Fin q)) (base : Nat) (node : (prepareNormalization q full).indexed.NodeId) (state : State) :
    let cache := (prepareNormalization q full).indexed
    (execute (queryROM q full stage used).semantic (nodeBlock full.length q base node.val) state).heap
      (base + node.val) = encodeTool ((IndexedDescent.leafTools cache).get node) := by
  intro cache
  rw [nodeBlock_heap, Function.update_self]
  let start := execute (queryROM q full stage used).semantic
    [.base (.constant .total 0), .base (.constant .value 0)] state
  have hs : start.register .total = 0 := rfl
  change (if (IndexedClosureRAM.execute _ _ start).register .total = 1 then _ else 0) = _
  rw [prepared_bits_total q full stage used node start, hs, Nat.zero_add, IndexedDescent.leafTools_get]
  cases ht : IndexedDescent.singletonTool (cache.decode node) with
  | none =>
    have hc : (cache.decode node).card ≠ 1 := by
      intro hc
      obtain ⟨tool, hsingle⟩ := Finset.card_eq_one.mp hc
      rw [hsingle, IndexedDescent.singletonTool_singleton] at ht
      cases ht
    rw [ite_eq_right hc]
    rfl
  | some tool =>
    have hsingle := IndexedDescent.singletonTool_spec (cache.decode node) tool ht
    have hc : (cache.decode node).card = 1 := by rw [hsingle]; exact Finset.card_singleton tool
    rw [ite_eq_left hc, prepared_bits_value_singleton q full stage used node tool hsingle start]
    rfl

theorem prepared_nodes_result (q : Nat) (full : List (Finset (Fin q))) (stage : Nat)
    (used : Finset (Fin q)) (base : Nat) (nodes : List Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (hm : node.val ∈ nodes) (state : State) :
    (execute (queryROM q full stage used).semantic (nodes.flatMap (nodeBlock full.length q base)) state).heap
      (base + node.val) = encodeTool ((IndexedDescent.leafTools (prepareNormalization q full).indexed).get node) := by
  induction nodes generalizing state with
  | nil => cases hm
  | cons other later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    by_cases hl : node.val ∈ later
    · exact ih hl _
    · have heq : node.val = other := (List.mem_cons.mp hm).resolve_right hl
      rw [nodes_frame _ _ _ _ later _ _ (by
        intro next hn he
        have hsame : node.val = next := Nat.add_left_cancel he
        exact hl (hsame ▸ hn)), ← heq]
      exact prepared_nodeBlock_result q full stage used base node state

theorem prepared_program_correct (q : Nat) (full : List (Finset (Fin q))) (stage : Nat)
    (used : Finset (Fin q)) (base : Nat) (state : State) :
    LabelsCorrect q full base (execute (queryROM q full stage used).semantic
      (program full.length q (prepareNormalization q full).indexed.nodes.size base) state).heap := by
  intro node
  exact prepared_nodes_result q full stage used base _ node (List.mem_range.mpr node.isLt) state

theorem totalQueryCost_le (N q size base : Nat) (hsize : 0 < size) :
    totalQueryCost q (program N q size base) ≤ 200 * queryWork q size := by
  rw [totalQueryCost, program_codeWords_length, List.length_append, program_trace_length, haltTrace_length]
  dsimp [queryWork]
  nlinarith

end PaperProofs.Structure.LaminarTree.PA17QueryLeafLabels012
