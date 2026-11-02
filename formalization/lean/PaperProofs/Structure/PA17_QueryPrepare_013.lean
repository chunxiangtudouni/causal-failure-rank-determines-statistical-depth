module

public import PaperProofs.Structure.PA17_QueryLeafLabels_012

/-! Recompute all tree/count/leaf data needed by a query from raw ROM,
without a Persistent hypothesis on the caller's arbitrary correct table. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryPrepare013

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def program (N q size metadataBase labelBase countsBase : Nat) : List Op :=
  PA17QueryMetadata010.program N q size metadataBase ++
    PA17LeafLabels005.program N q size labelBase ++
    PA17QueryCounts008.program N q size countsBase

theorem prepared_program_correct (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (stage : Nat) (used : Finset (Fin q))
    (metadataBase labelBase countsBase : Nat)
    (hlabel : metadataBase + 3 * (prepareNormalization q full).indexed.nodes.size + 1 ≤ labelBase)
    (hcounts : labelBase + (prepareNormalization q full).indexed.nodes.size ≤ countsBase)
    (state : State) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let result := execute (queryROM q full stage used).semantic
      (program full.length q size metadataBase labelBase countsBase) state
    UniformTreeMetadataRAM.MetadataCorrect q full metadataBase result.heap ∧
      PA17LeafLabels005.LabelsCorrect q full labelBase result.heap ∧
      PA17QueryCounts008.CountsCorrect q full used countsBase result.heap := by
  intro size result
  let rom := (queryROM q full stage used).semantic
  let metadataPass := PA17QueryMetadata010.program full.length q size metadataBase
  let leaf := PA17LeafLabels005.program full.length q size labelBase
  let counts := PA17QueryCounts008.program full.length q size countsBase
  let afterMeta := execute rom metadataPass state
  let afterLeaf := execute rom leaf afterMeta
  have hresult : result = execute rom counts afterLeaf := by
    simp only [result, program, IndexedClosureRAM.execute_append, afterLeaf, afterMeta,
      metadataPass, leaf, counts, rom]
  have hm := PA17QueryMetadata010.prepared_program_metadata q full hq hlaminar stage used metadataBase state
  have hl := PA17QueryLeafLabels012.prepared_program_correct q full stage used labelBase afterMeta
  have hc := PA17QueryCounts008.prepared_program_correct q full stage used countsBase afterLeaf
  have hframe (address : Nat) (ha : address < labelBase) : result.heap address = afterMeta.heap address := by
    have hcounts' : address < countsBase := by
      change labelBase + size ≤ countsBase at hcounts
      omega
    change (execute rom (program full.length q size metadataBase labelBase countsBase) state).heap address = _
    rw [program, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
    have hcframe := PA17QueryCounts008.program_take_frame rom full.length q size countsBase counts.length
      afterLeaf address (Or.inl hcounts')
    change (execute rom (counts.take counts.length) afterLeaf).heap address = afterLeaf.heap address at hcframe
    rw [List.take_length] at hcframe
    rw [hcframe]
    have hlframe := PA17LeafLabels005.program_take_frame rom full.length q size labelBase leaf.length
      afterMeta address (Or.inl ha)
    change (execute rom (leaf.take leaf.length) afterMeta).heap address = afterMeta.heap address at hlframe
    rwa [List.take_length] at hlframe
  constructor
  · constructor
    · rw [hframe _ (by dsimp [UniformTreeMetadataRAM.parentAddress]; change metadataBase + 3 * size + 1 ≤ labelBase at hlabel; omega)]
      exact hm.1
    · intro node
      have hn : node.val < size := node.isLt
      have hm' : metadataBase + 3 * size + 1 ≤ labelBase := hlabel
      rw [hframe _ (by dsimp [UniformTreeMetadataRAM.cardAddress]; omega),
        hframe _ (by dsimp [UniformTreeMetadataRAM.parentAddress]; omega),
        hframe _ (by dsimp [UniformTreeMetadataRAM.internalAddress]; omega)]
      exact hm.2 node
  constructor
  · intro node
    have hf := PA17QueryCounts008.program_take_frame rom full.length q size countsBase counts.length afterLeaf
      (labelBase + node.val) (Or.inl (by
        have hn : node.val < size := node.isLt
        change labelBase + size ≤ countsBase at hcounts
        omega))
    change (execute rom (counts.take counts.length) afterLeaf).heap _ = _ at hf
    rw [List.take_length] at hf
    rw [hresult]
    rw [hf]
    exact hl node
  · rw [hresult]
    exact hc

theorem program_prefixFrame (rom : ROM) (N q size metadataBase labelBase countsBase address : Nat)
    (hm : address < metadataBase) (hl : address < labelBase) (hc : address < countsBase) :
    UniformFreeTableSafety.PrefixFrame rom (program N q size metadataBase labelBase countsBase) address := by
  rw [program]
  apply UniformFreeTableSafety.PrefixFrame.append rom _ _ address
  · apply UniformFreeTableSafety.PrefixFrame.append rom _ _ address
    · intro state count _
      exact PA17QueryMetadata010.program_take_frame rom N q size metadataBase count state address hm
    · intro state count _
      exact PA17LeafLabels005.program_take_frame rom N q size labelBase count state address (Or.inl hl)
  · intro state count _
    exact PA17QueryCounts008.program_take_frame rom N q size countsBase count state address (Or.inl hc)

theorem program_capacityThroughout (q capWords N size metadataBase labelBase countsBase : Nat)
    (rom : PhysicalROM) (hm : capWords ≤ metadataBase) (hl : capWords ≤ labelBase) (hc : capWords ≤ countsBase)
    (state : State) (hcapacity : CapacityPrefixBounded q capWords state.heap) :
    CapacityThroughout q capWords rom (program N q size metadataBase labelBase countsBase) state := by
  intro count hcount address ha
  rw [program_prefixFrame rom.semantic N q size metadataBase labelBase countsBase address
    (by omega) (by omega) (by omega) state count hcount]
  exact hcapacity address ha

theorem totalQueryCost_append_le (q : Nat) (left right : List Op) :
    totalQueryCost q (left ++ right) ≤ totalQueryCost q left + totalQueryCost q right := by
  simp only [totalQueryCost, haltingWords_length, List.length_append, IndexedClosureRAM.trace_append]
  omega

theorem program_totalQueryCost_le (N q size metadataBase labelBase countsBase : Nat) (hsize : 0 < size) :
    totalQueryCost q (program N q size metadataBase labelBase countsBase) ≤ 760 * queryWork q size := by
  have hm := PA17QueryMetadata010.totalQueryCost_le N q size metadataBase hsize
  have hl := PA17QueryLeafLabels012.totalQueryCost_le N q size labelBase hsize
  have hc := PA17QueryCounts008.totalQueryCost_le N q size countsBase hsize
  have ha := totalQueryCost_append_le q (PA17QueryMetadata010.program N q size metadataBase)
    (PA17LeafLabels005.program N q size labelBase)
  have hb := totalQueryCost_append_le q
    (PA17QueryMetadata010.program N q size metadataBase ++ PA17LeafLabels005.program N q size labelBase)
    (PA17QueryCounts008.program N q size countsBase)
  change _ ≤ 760 * queryWork q size
  unfold program
  omega

end PaperProofs.Structure.LaminarTree.PA17QueryPrepare013
