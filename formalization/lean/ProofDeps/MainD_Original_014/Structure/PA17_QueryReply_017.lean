module

public import Structure.PA17_QueryRanks_011
public import Structure.PA17_QueryLayout_014

/-! Decode the actually scanned budget word into the original selectedBudget,
then transport the actual selector output to the original query reply. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryReply017

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def encodeTool {q : Nat} : Option (Fin q) → Nat
  | none => 0
  | some tool => tool.val + 1

def selectedFromWord {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId) (word : Nat) : Option (Fin q) :=
  if word = 0 then none else IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row (word - 1))

theorem selectedFromWord_eq_maximizingTool {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId) :
    selectedFromWord cache leaves counts row node
      (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node)) =
      IndexedQuery.maximizingTool cache leaves counts row node := by
  rw [← PA17QueryRanks011.selectedBudget_word]
  unfold selectedFromWord IndexedQuery.maximizingTool
  cases hs : IndexedQuery.selectedBudget q (IndexedQuery.budgetExtensionTest cache counts row node) with
  | none => rfl
  | some budget =>
    simp only [PA17QueryRanks011.optionBudgetWord, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ite_false, Nat.add_sub_cancel, Option.bind_some]

theorem selector_control_eq_maximizingTool {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId)
    (state : State) (header toolAddress : Nat)
    (hbudget : state.heap (header + 6) =
      PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1)
    (hflag : state.heap (header + 7) = if state.heap (header + 2) = 0 then 0 else
      if PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) = 0 then 0 else 1)
    (htool : state.heap toolAddress = if state.heap (header + 7) = 0 then 0 else
      encodeTool (IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row (state.heap (header + 6))))) :
    state.heap toolAddress = if state.heap (header + 2) = 0 then 0 else
      encodeTool (IndexedQuery.maximizingTool cache leaves counts row node) := by
  rw [htool, hflag, hbudget, ← selectedFromWord_eq_maximizingTool]
  by_cases ha : state.heap (header + 2) = 0
  · simp only [ha, ite_true]
  · simp only [ha, ite_false]
    by_cases hz : PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) = 0
    · simp only [hz, ite_true, selectedFromWord, encodeTool]
    · simp only [hz, ite_false, Nat.one_ne_zero, selectedFromWord]

theorem replyProgram_query {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId)
    (rom : ROM) (state : State) (header toolAddress : Nat)
    (hgood : state.heap (header + 4) = PA17QueryRanks011.firstFalseValue q
      (fun budget => IndexedQuery.accepts cache counts (IndexedQuery.entryAt row budget)))
    (hbad : state.heap (header + 5) = PA17QueryRanks011.firstFalseValue q
      (IndexedQuery.budgetExtensionTest cache counts row node))
    (hbudget : state.heap (header + 6) =
      PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1)
    (hflag : state.heap (header + 7) = if state.heap (header + 2) = 0 then 0 else
      if PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) = 0 then 0 else 1)
    (htool : state.heap toolAddress = if state.heap (header + 7) = 0 then 0 else
      encodeTool (IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row (state.heap (header + 6))))) :
    ReplyCorrect q
      (if state.heap (header + 2) = 0 then IndexedQuery.terminalReply q else
        IndexedQuery.query cache leaves counts row node)
      (execute rom (PA17QueryRanks011.replyProgram q header toolAddress) state) := by
  have ht := selector_control_eq_maximizingTool cache leaves counts row node state header toolAddress hbudget hflag htool
  by_cases ha : state.heap (header + 2) = 0
  · obtain ⟨hg, hb, hr, hi⟩ := PA17QueryRanks011.replyProgram_registers q header toolAddress rom state
    simp only [ha, ite_true] at hg hb hr hi ⊢
    exact ⟨hr, hg, hb, hi⟩
  · rw [ite_eq_right ha] at ht ⊢
    have hr := PA17QueryRanks011.replyProgram_correct rom header toolAddress state
      (fun budget => IndexedQuery.accepts cache counts (IndexedQuery.entryAt row budget))
      (IndexedQuery.budgetExtensionTest cache counts row node)
      (IndexedQuery.maximizingTool cache leaves counts row node) hgood hbad ht
    simpa only [ha, ite_false, IndexedQuery.query, IndexedQuery.goodRank, IndexedQuery.badRank] using hr

theorem replyProgram_totalQueryCost_le (q size header toolAddress : Nat) (hsize : 0 < size) :
    totalQueryCost q (PA17QueryRanks011.replyProgram q header toolAddress) ≤ 300 * queryWork q size := by
  rw [totalQueryCost, haltingWords_length, PA17QueryRanks011.replyProgram_length,
    List.length_append, PA17QueryRanks011.replyProgram_trace_length, haltTrace_length]
  dsimp [queryWork]
  nlinarith

end PaperProofs.Structure.LaminarTree.PA17QueryReply017
