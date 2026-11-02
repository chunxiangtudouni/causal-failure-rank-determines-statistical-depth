module

public import Structure.PA17_A19QueryBridge_RuntimeReplyCorrect_022a
public import Init.Data.List.Nat.Range

/-! The genuine first-false minimum certifies the selected predecessor row.
This holds for arbitrary tests,without monotonicity/spectrum assumptions.
Consequently an enabled raw payload descent needs no runtime tag getter. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022

open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem firstFalseValue_true_below (q : Nat) (test : Nat → Bool) (index : Nat)
    (hi : index < PA17QueryRanks011.firstFalseValue q test) : test index = true := by
  cases hfind : IndexedQuery.firstFalse q test with
  | none =>
    have hword : PA17QueryRanks011.firstFalseValue q test = q + 2 := by
      simp only [PA17QueryRanks011.firstFalseValue, hfind, Option.getD_none]
    have hbound : index < q + 2 := by omega
    have hnone := List.find?_range'_eq_none.mp hfind
    have htest := hnone index (Nat.zero_le _) (by omega)
    simpa only [Bool.not_not] using htest
  | some first =>
    have hword : PA17QueryRanks011.firstFalseValue q test = first := by
      simp only [PA17QueryRanks011.firstFalseValue, hfind, Option.getD_some]
    have hminimal := (List.find?_range'_eq_some.mp hfind).2.2
    have htest := hminimal index (Nat.zero_le _) (by omega)
    simpa only [Bool.not_not] using htest

theorem firstFalseValue_prev_true (q : Nat) (test : Nat → Bool)
    (hb : PA17QueryRanks011.firstFalseValue q test ≠ 0) :
    test (PA17QueryRanks011.firstFalseValue q test - 1) = true := by
  exact firstFalseValue_true_below q test _ (by omega)

theorem selected_entry_vector {q : Nat} (cache : IndexedNodeCache (Fin q))
    (counts : IndexedCapacity cache) (row : IndexedTable.Row cache (q + 1))
    (node : Option cache.NodeId)
    (hb : PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) ≠ 0) :
    ∃ capacity : IndexedCapacity cache, IndexedQuery.entryAt row
      (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1) = .vector capacity := by
  have htest := firstFalseValue_prev_true q (IndexedQuery.budgetExtensionTest cache counts row node) hb
  cases hentry : IndexedQuery.entryAt row
      (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1) with
  | void =>
    simp only [IndexedQuery.budgetExtensionTest, hentry, IndexedQuery.extensionTest, Bool.false_eq_true] at htest
  | vector capacity => exact ⟨capacity, rfl⟩

theorem raw_payload_select_eq {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId) (payload : IndexedCapacity cache)
    (hb : PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) ≠ 0)
    (hpayload : ∀ capacity : IndexedCapacity cache,
      IndexedQuery.entryAt row
        (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1) = .vector capacity →
      payload = capacity) :
    node.bind (IndexedDescent.selectAt cache leaves counts payload) =
      IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row
        (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1)) := by
  obtain ⟨capacity, hentry⟩ := selected_entry_vector cache counts row node hb
  rw [hentry, IndexedQuery.selectEntry, hpayload capacity hentry]

theorem leafLabels_encodeTool_eq {q : Nat} (tool : Option (Fin q)) :
    PA17LeafLabels005.encodeTool tool = PA17QueryReply017.encodeTool tool := by
  cases tool <;> rfl

theorem raw_payload_encodeTool_eq {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId) (payload : IndexedCapacity cache)
    (hb : PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) ≠ 0)
    (hpayload : ∀ capacity : IndexedCapacity cache,
      IndexedQuery.entryAt row
        (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1) = .vector capacity →
      payload = capacity) :
    PA17LeafLabels005.encodeTool (node.bind (IndexedDescent.selectAt cache leaves counts payload)) =
      PA17QueryReply017.encodeTool (IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row
        (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1))) := by
  rw [leafLabels_encodeTool_eq, raw_payload_select_eq cache leaves counts row node payload hb hpayload]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022
