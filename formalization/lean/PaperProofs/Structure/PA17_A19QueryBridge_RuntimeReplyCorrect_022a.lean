module

public import PaperProofs.Structure.PA17_QueryReply_017
public import PaperProofs.Structure.PA17_QueryBudget_015
public import PaperProofs.Structure.CompactControllerClaims

/-! Pure reply algebra for the genuine Word footer. No Nat reply program is
executed here; these lemmas identify the four already-produced register values
with ORIGINAL query/callback semantics, including the real final tool mask. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022

open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem encodeTool_le {q : Nat} (tool : Option (Fin q)) : PA17QueryReply017.encodeTool tool ≤ q := by
  cases tool with
  | none => simp only [PA17QueryReply017.encodeTool]; omega
  | some tool => change tool.val + 1 ≤ q; exact tool.isLt

theorem masked_select_eq_maximizingTool {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId) :
    let b := PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node)
    (if b = 0 then 0 else PA17QueryReply017.encodeTool
      (IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row (b - 1)))) =
      PA17QueryReply017.encodeTool (IndexedQuery.maximizingTool cache leaves counts row node) := by
  have ht := congrArg PA17QueryReply017.encodeTool
    (PA17QueryReply017.selectedFromWord_eq_maximizingTool cache leaves counts row node)
  dsimp only
  by_cases hz : PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) = 0
  · simpa only [PA17QueryReply017.selectedFromWord, hz, ite_true, PA17QueryReply017.encodeTool] using ht
  · simpa only [PA17QueryReply017.selectedFromWord, hz, ite_false] using ht

theorem registers_reply_correct {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId) (active : Nat) (state : State) :
    let good : Nat → Bool := fun budget => IndexedQuery.accepts cache counts (IndexedQuery.entryAt row budget)
    let bad := IndexedQuery.budgetExtensionTest cache counts row node
    let g := PA17QueryRanks011.firstFalseValue q good
    let b := PA17QueryRanks011.firstFalseValue q bad
    state.register .old = (if active = 0 then q + 2 else g) →
    state.register .fresh = (if active = 0 then 0 else b) →
    state.register .value = (if active = 0 then q + 2 else min g (b + 1)) →
    state.register .index = (if active = 0 then 0 else if b = 0 then 0 else
      PA17QueryReply017.encodeTool (IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row (b - 1)))) →
    ReplyCorrect q (if active = 0 then IndexedQuery.terminalReply q else
      IndexedQuery.query cache leaves counts row node) state := by
  dsimp only
  intro hold hfresh hvalue hindex
  let good : Nat → Bool := fun budget => IndexedQuery.accepts cache counts (IndexedQuery.entryAt row budget)
  let bad := IndexedQuery.budgetExtensionTest cache counts row node
  by_cases ha : active = 0
  · simp only [ha, ite_true] at hold hfresh hvalue hindex ⊢
    exact ⟨hvalue, hold, hfresh, hindex⟩
  · simp only [ha, ite_false] at hold hfresh hvalue hindex ⊢
    change state.register .value = encodeRank q (min (IndexedQuery.rankFromTests q good) (1 + IndexedQuery.rankFromTests q bad)) ∧
      state.register .old = encodeRank q (IndexedQuery.rankFromTests q good) ∧
      state.register .fresh = encodeRank q (IndexedQuery.rankFromTests q bad) ∧
      state.register .index = PA17QueryReply017.encodeTool (IndexedQuery.maximizingTool cache leaves counts row node)
    exact ⟨hvalue.trans (PA17QueryRanks011.encode_currentRank q good bad).symm,
      hold.trans (PA17QueryRanks011.firstFalseValue_eq_encodeRank q good),
      hfresh.trans (PA17QueryRanks011.firstFalseValue_eq_encodeRank q bad),
      hindex.trans (masked_select_eq_maximizingTool cache leaves counts row node)⟩

theorem callback_eq_original_query {q : Nat} (full : List (Finset (Fin q)))
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (hq : 0 < q) :
    CompactControllerClaims.callback q full stage used =
      if PA17QueryHeader009.active full.length stage.val = 0 then IndexedQuery.terminalReply q else
        IndexedQuery.query (prepareNormalization q full).indexed
          (IndexedDescent.leafTools (prepareNormalization q full).indexed)
          (IndexedDescent.usedCounts (prepareNormalization q full).indexed used)
          (IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage))
          (PA17QueryBudget015.node full hq stage) := by
  by_cases hs : stage.val < full.length
  · simp [CompactControllerClaims.callback, hq, expectedReply, PA17QueryHeader009.active, hs,
      PA17QueryBudget015.rowIndex, PA17QueryBudget015.node]
  · simp [CompactControllerClaims.callback, hq, expectedReply, PA17QueryHeader009.active, hs]

theorem callback_registers_correct {q : Nat} (full : List (Finset (Fin q)))
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (hq : 0 < q) (state : State) :
    let cache := (prepareNormalization q full).indexed
    let leaves := IndexedDescent.leafTools cache
    let counts := IndexedDescent.usedCounts cache used
    let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
    let node := PA17QueryBudget015.node full hq stage
    let active := PA17QueryHeader009.active full.length stage.val
    let g := PA17QueryRanks011.firstFalseValue q (fun budget => IndexedQuery.accepts cache counts (IndexedQuery.entryAt row budget))
    let b := PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node)
    state.register .old = (if active = 0 then q + 2 else g) →
    state.register .fresh = (if active = 0 then 0 else b) →
    state.register .value = (if active = 0 then q + 2 else min g (b + 1)) →
    state.register .index = (if active = 0 then 0 else if b = 0 then 0 else
      PA17QueryReply017.encodeTool (IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row (b - 1)))) →
    ReplyCorrect q (CompactControllerClaims.callback q full stage used) state := by
  dsimp only
  intro hold hfresh hvalue hindex
  rw [callback_eq_original_query full stage used hq]
  exact registers_reply_correct _ _ _ _ _ _ _ hold hfresh hvalue hindex

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022
