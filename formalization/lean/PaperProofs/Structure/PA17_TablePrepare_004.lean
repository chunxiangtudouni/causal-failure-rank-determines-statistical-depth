module

public import PaperProofs.Structure.PA17_CellLayout_003
public import PaperProofs.Structure.PA17_MetadataAssembly_003
public import PaperProofs.Structure.PA17_TerminalRow_002

/-! Actual metadata/stage construction followed by terminal/budget-zero
initialization, in the concrete persistent cell layout. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17TablePrepare004

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17TagBridge001
open PA17CellLayout003

def program (N q size : Nat) : List Op :=
  PA17MetadataAssembly003.program N q size (capacityWords N q size) ++
    PA17TerminalRow002.freeSlots size (capacityWords N q size) (PA17TerminalRow002.seedSlots N q)

theorem seedSlots_bound (N q size slot : Nat) (hs : slot ∈ PA17TerminalRow002.seedSlots N q) :
    (slot + 1) * (size + 1) ≤ capacityWords N q size := by
  exact (PA17TerminalRow002.seedSlots_words_bound N q size slot hs).trans (table_le_capacityWords N q size)

theorem freeSlots_index_frame (rom : ROM) (N q size : Nat) (state : State)
    (address : Nat) (ha : capacityWords N q size ≤ address) :
    (execute rom (PA17TerminalRow002.freeSlots size (capacityWords N q size)
      (PA17TerminalRow002.seedSlots N q)) state).heap address = state.heap address :=
  PA17TerminalRow002.freeSlots_metadata_frame rom size _ _ (seedSlots_bound N q size) state address ha

theorem prepared_program_correct (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (state : State) :
    let N := full.length
    let cache := (prepareNormalization q full).indexed
    let size := cache.nodes.size
    let result := execute (givenTreeROM q full).semantic (program N q size) state
    UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase N q size) result.heap ∧
      PA17StageMap001.StageMapCorrect q full hq (stageBase N q size) result.heap ∧
      ∀ slot ∈ PA17TerminalRow002.seedSlots N q,
        TagFirstRep cache result.heap (slot * (size + 1)) (IndexedEntry.free cache) := by
  intro N cache size result
  let before := execute (givenTreeROM q full).semantic
    (PA17MetadataAssembly003.program N q size (capacityWords N q size)) state
  have hm := PA17MetadataAssembly003.prepared_program_correct q full hq hlaminar (capacityWords N q size) state
  have hframe (address : Nat) (ha : capacityWords N q size ≤ address) :
      result.heap address = before.heap address := by
    change (execute (givenTreeROM q full).semantic (program N q size) state).heap address = _
    rw [program, IndexedClosureRAM.execute_append]
    exact freeSlots_index_frame _ N q size before address ha
  constructor
  · constructor
    · rw [hframe _ (by dsimp [UniformTreeMetadataRAM.parentAddress, metadataBase]; omega)]
      exact hm.1.1
    · intro node
      rw [hframe _ (by dsimp [UniformTreeMetadataRAM.cardAddress, metadataBase]; omega),
        hframe _ (by dsimp [UniformTreeMetadataRAM.parentAddress, metadataBase]; omega),
        hframe _ (by dsimp [UniformTreeMetadataRAM.internalAddress, metadataBase]; omega)]
      exact hm.1.2 node
  constructor
  · intro stage
    rw [hframe _ (by dsimp [stageBase, metadataBase]; omega)]
    exact hm.2 stage
  · intro slot hs
    change TagFirstRep cache (execute (givenTreeROM q full).semantic (program N q size) state).heap _ _
    rw [program, IndexedClosureRAM.execute_append]
    exact PA17TerminalRow002.freeSlots_rep cache _ (capacityWords N q size) _ (seedSlots_bound N q size)
      before (fun node => (hm.1.2 node).1) slot hs

theorem prepared_program_capacityThroughout (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (state : State)
    (hcapacity : CapacityPrefixBounded q
      (capacityWords full.length q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    CapacityThroughout q (capacityWords full.length q size) (givenTreeROM q full)
      (program full.length q size) state := by
  intro size
  let cap := capacityWords full.length q size
  let metadata := PA17MetadataAssembly003.program full.length q size cap
  have hl := PA17MetadataAssembly003.leading_capacityThroughout (givenTreeROM q full) full.length q size cap state hcapacity
  rw [program]
  apply UniformFreeTableSafety.capacityThroughout_append q cap (givenTreeROM q full) _ _ state hl
  apply PA17TerminalRow002.freeSlots_capacityThroughout q cap size cap hq (givenTreeROM q full) _
    (seedSlots_bound full.length q size) _
    (by
      have hh := hl (PA17MetadataAssembly003.program full.length q size cap).length le_rfl
      rw [List.take_length] at hh
      exact hh)
  intro node hn
  exact UniformTreeMetadataRAM.metadata_card_bound q full cap _
    (PA17MetadataAssembly003.prepared_program_correct q full hq hlaminar cap state).1 ⟨node, hn⟩

theorem prepared_program_budgetZero (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (state : State) (stage : Fin (full.length + 1)) :
    let cache := (prepareNormalization q full).indexed
    readEntry cache.nodes.size (stage.val * (q + 2))
      (execute (givenTreeROM q full).semantic (program full.length q cache.nodes.size) state).heap =
        (IndexedQuery.storedPositiveRow q full stage).get ⟨0, by omega⟩ := by
  intro cache
  rw [PA17TerminalRow002.storedPositiveRow_budgetZero]
  apply readEntry_eq_of_rep
  apply (prepared_program_correct q full hq hlaminar state).2.2
  rw [PA17TerminalRow002.seedSlots, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨stage.val, List.mem_range.mpr stage.isLt, rfl⟩)

theorem prepared_program_terminal (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (state : State) (budget : Fin (q + 2)) :
    let cache := (prepareNormalization q full).indexed
    readEntry cache.nodes.size (full.length * (q + 2) + budget.val)
      (execute (givenTreeROM q full).semantic (program full.length q cache.nodes.size) state).heap =
        (IndexedQuery.storedPositiveRow q full ⟨full.length, by omega⟩).get budget := by
  intro cache
  rw [PA17TerminalRow002.storedPositiveRow_terminal, IndexedTable.terminalRow_get]
  apply readEntry_eq_of_rep
  apply (prepared_program_correct q full hq hlaminar state).2.2
  rw [PA17TerminalRow002.seedSlots, List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨budget.val, List.mem_range.mpr budget.isLt, rfl⟩)

theorem prepared_program_tags (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (state : State)
    (htags : ∀ slot < cells full.length q,
      state.heap (slot * ((prepareNormalization q full).indexed.nodes.size + 1)) ≤ 1) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ∀ slot < cells full.length q,
      (execute (givenTreeROM q full).semantic (program full.length q size) state).heap (slot * (size + 1)) ≤ 1 := by
  intro size slot hs
  by_cases hm : slot ∈ PA17TerminalRow002.seedSlots full.length q
  · have hr := (prepared_program_correct q full hq hlaminar state).2.2 slot hm
    change _ = 1 ∧ _ at hr
    rw [hr.1]
  · rw [program, IndexedClosureRAM.execute_append,
      PA17TerminalRow002.freeSlots_frame _ size _ _ _ (slot * (size + 1)) (by
        intro other ho index hi
        have hne : slot ≠ other := by intro he; exact hm (he ▸ ho)
        simpa only [PA17TerminalRow002.slotBase, Nat.add_zero] using
          PA17TerminalRow002.slotBase_disjoint size slot other hne 0 index (Nat.zero_le _) hi)]
    have hh := PA17MetadataAssembly003.leading_take_frame (givenTreeROM q full).semantic full.length q size
      (capacityWords full.length q size) (PA17MetadataAssembly003.program full.length q size
        (capacityWords full.length q size)).length state (slot * (size + 1))
      ((table_slot_bound full.length q size slot hs 0 (Nat.zero_le _)).trans_le (table_le_capacityWords _ _ _))
    rw [List.take_length] at hh
    rw [hh]
    exact htags slot hs

theorem program_trace_length (N q size : Nat) :
    (trace (program N q size)).length =
      (30 * q + 131) * size + 27 + N * ((82 * q + 28) * size + 27) +
        (N + q + 3) * (38 * size + 27) := by
  rw [program, IndexedClosureRAM.trace_append, List.length_append,
    PA17MetadataAssembly003.program_trace_length, PA17TerminalRow002.freeSlots_trace_length,
    PA17TerminalRow002.seedSlots_length]

theorem program_trace_le (N q size : Nat) (hsize : 0 < size) :
    (trace (program N q size) ++ haltTrace).length ≤ 460 * work N q size := by
  have hm := PA17MetadataAssembly003.program_trace_le N q size (capacityWords N q size) hsize
  rw [List.length_append] at hm ⊢
  rw [program, IndexedClosureRAM.trace_append, List.length_append]
  have hs : (trace (PA17TerminalRow002.freeSlots size (capacityWords N q size)
      (PA17TerminalRow002.seedSlots N q))).length ≤ 260 * work N q size := by
    rw [PA17TerminalRow002.freeSlots_trace_length, PA17TerminalRow002.seedSlots_length]
    have hcoeff : N + q + 3 ≤ 4 * ((N + 1) * (q + 1)) := by nlinarith
    have hsize' : 38 * size + 27 ≤ 65 * size := by omega
    have hh := Nat.mul_le_mul hcoeff hsize'
    dsimp [work]
    nlinarith
  omega

end PaperProofs.Structure.LaminarTree.PA17TablePrepare004
