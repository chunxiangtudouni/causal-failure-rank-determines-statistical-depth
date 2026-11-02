module

public import PaperProofs.Structure.PA17_QueryPrepare_013
public import PaperProofs.Structure.PA17_CellLayout_003

/-! The concrete query allocation and actual preparation on arbitrary
incoming heaps. Query-only data are rebuilt; the table is never rewritten. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryLayout014

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def capacityWords (N q size : Nat) : Nat := PA17CellLayout003.capacityWords N q size
def metadataBase (N q size : Nat) : Nat := capacityWords N q size
def parentBase (N q size : Nat) : Nat := metadataBase N q size + size
def labelBase (N q size : Nat) : Nat := metadataBase N q size + 3 * size + 1 + N
def countsBase (N q size : Nat) : Nat := labelBase N q size + size
def header (N q size : Nat) : Nat := countsBase N q size + size
def goodFlags (N q size : Nat) : Nat := header N q size + 16
def badFlags (N q size : Nat) : Nat := goodFlags N q size + q + 2
def childBase (N q size : Nat) : Nat := badFlags N q size + q + 2
def payloadPointerAddress (N q size : Nat) : Nat := childBase N q size + size + 1
def toolAddress (N q size : Nat) : Nat := childBase N q size + size + 2
def indexWords (N q size : Nat) : Nat := 6 * size + N + 2 * q + 24
def heapWords (N q size : Nat) : Nat := capacityWords N q size + indexWords N q size

theorem toolAddress_end (N q size : Nat) : toolAddress N q size + 1 = heapWords N q size := by
  dsimp [toolAddress, childBase, badFlags, goodFlags, header, countsBase, labelBase, metadataBase, heapWords, indexWords]
  omega

theorem indexWords_le (N q size : Nat) : indexWords N q size ≤ 24 * (N + q + size + 1) := by
  dsimp [indexWords]
  omega

theorem build_indices_fit (N q size : Nat) : PA17MetadataAssembly003.indexWords N size ≤ indexWords N q size := by
  dsimp [PA17MetadataAssembly003.indexWords, indexWords]
  omega

theorem metadata_before_labels (N q size : Nat) : metadataBase N q size + 3 * size + 1 ≤ labelBase N q size := by
  dsimp [labelBase]
  omega

theorem labels_before_counts (N q size : Nat) : labelBase N q size + size = countsBase N q size := rfl

theorem counts_before_header (N q size : Nat) : countsBase N q size + size = header N q size := rfl

theorem prepared_regions_below_flags (N q size : Nat) :
    metadataBase N q size + 3 * size + 1 ≤ goodFlags N q size ∧
      countsBase N q size + size ≤ goodFlags N q size ∧
      header N q size + 9 ≤ goodFlags N q size := by
  dsimp [goodFlags, header, countsBase, labelBase]
  omega

theorem flags_disjoint (N q size left right : Nat) (hl : left < q + 2) (_hr : right < q + 2) :
    goodFlags N q size + left ≠ badFlags N q size + right := by
  dsimp [badFlags]
  omega

theorem capacity_before_queryRegions (N q size : Nat) :
    capacityWords N q size ≤ metadataBase N q size ∧
      capacityWords N q size ≤ labelBase N q size ∧
      capacityWords N q size ≤ countsBase N q size ∧
      capacityWords N q size ≤ header N q size ∧
      capacityWords N q size ≤ goodFlags N q size ∧
      capacityWords N q size ≤ badFlags N q size ∧
      capacityWords N q size ≤ childBase N q size := by
  dsimp [metadataBase, labelBase, countsBase, header, goodFlags, badFlags, childBase]
  omega

def prepareProgram (N q size : Nat) : List Op :=
  PA17QueryPrepare013.program N q size (metadataBase N q size) (labelBase N q size) (countsBase N q size)

theorem prepared_prepareProgram_correct (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (stage : Nat) (used : Finset (Fin q)) (state : State) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let result := execute (queryROM q full stage used).semantic (prepareProgram full.length q size) state
    UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase full.length q size) result.heap ∧
      PA17LeafLabels005.LabelsCorrect q full (labelBase full.length q size) result.heap ∧
      PA17QueryCounts008.CountsCorrect q full used (countsBase full.length q size) result.heap :=
  PA17QueryPrepare013.prepared_program_correct q full hq hlaminar stage used _ _ _
    (metadata_before_labels _ _ _) (labels_before_counts _ _ _).le state

theorem prepareProgram_prefixFrame (rom : ROM) (N q size address : Nat)
    (ha : address < capacityWords N q size) :
    UniformFreeTableSafety.PrefixFrame rom (prepareProgram N q size) address := by
  have hb := capacity_before_queryRegions N q size
  exact PA17QueryPrepare013.program_prefixFrame rom _ _ _ _ _ _ address (ha.trans_le hb.1)
    (ha.trans_le hb.2.1) (ha.trans_le hb.2.2.1)

theorem prepareProgram_table_take_frame (rom : ROM) (N q size count : Nat) (state : State)
    (address : Nat) (ha : address < tableWords N q size) :
    (execute rom ((prepareProgram N q size).take count) state).heap address = state.heap address := by
  have hc := PA17CellLayout003.table_le_capacityWords N q size
  by_cases hn : count ≤ (prepareProgram N q size).length
  · exact prepareProgram_prefixFrame rom N q size address (ha.trans_le hc) state count hn
  · rw [List.take_of_length_le (by omega)]
    have hf := prepareProgram_prefixFrame rom N q size address (ha.trans_le hc) state (prepareProgram N q size).length le_rfl
    simpa only [List.take_length] using hf

theorem prepareProgram_capacityThroughout (q N size : Nat) (rom : PhysicalROM) (state : State)
    (hcapacity : CapacityPrefixBounded q (capacityWords N q size) state.heap) :
    CapacityThroughout q (capacityWords N q size) rom (prepareProgram N q size) state := by
  intro count hc address ha
  rw [prepareProgram_prefixFrame rom.semantic N q size address ha state count hc]
  exact hcapacity address ha

theorem readEntry_congr (size slot : Nat) (old fresh : Nat → Nat)
    (hframe : ∀ index ≤ size, fresh (slot * (size + 1) + index) = old (slot * (size + 1) + index)) :
    readEntry size slot fresh = readEntry size slot old := by
  have htag : fresh (slot * (size + 1)) = old (slot * (size + 1)) := by
    simpa only [Nat.add_zero] using hframe 0 (Nat.zero_le _)
  simp only [readEntry, htag]
  split_ifs
  · rfl
  · apply congrArg CapacityBits.Entry.vector
    apply Vector.ext
    intro index hi
    change (Vector.ofFn _).get ⟨index, hi⟩ = (Vector.ofFn _).get ⟨index, hi⟩
    rw [cache_get_ofFn, cache_get_ofFn]
    simpa only [Nat.add_assoc] using hframe (1 + index) (by omega)

theorem prepareProgram_readEntry_frame (rom : ROM) (N q size slot : Nat) (hs : slot < cells N q) (state : State) :
    readEntry size slot (execute rom (prepareProgram N q size) state).heap = readEntry size slot state.heap := by
  apply readEntry_congr
  intro index hi
  have hf := prepareProgram_table_take_frame rom N q size (prepareProgram N q size).length state
    (slot * (size + 1) + index) (PA17CellLayout003.table_slot_bound N q size slot hs index hi)
  simpa only [List.take_length] using hf

theorem prepareProgram_physicalTableCorrect (q : Nat) (full : List (Finset (Fin q)))
    (stage : Nat) (used : Finset (Fin q)) (state : State) (htable : PhysicalTableCorrect q full state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    PhysicalTableCorrect q full (execute (queryROM q full stage used).semantic (prepareProgram full.length q size) state).heap := by
  intro size
  constructor
  · intro row budget
    rw [prepareProgram_readEntry_frame _ _ _ _ _ (by
      dsimp [cells]
      calc
        row.val * (q + 2) + budget.val < row.val * (q + 2) + (q + 2) :=
          Nat.add_lt_add_left budget.isLt _
        _ = (row.val + 1) * (q + 2) := by ring
        _ ≤ (full.length + 1) * (q + 2) := Nat.mul_le_mul_right _ (by have := row.isLt; omega))]
    exact htable.1 row budget
  · intro slot hs
    have hf := prepareProgram_table_take_frame (queryROM q full stage used).semantic full.length q size
      (prepareProgram full.length q size).length state (slot * (size + 1))
      (by simpa only [Nat.add_zero] using PA17CellLayout003.table_slot_bound full.length q size slot hs 0 (Nat.zero_le _))
    rw [List.take_length] at hf
    rw [hf]
    exact htable.2 slot hs

theorem prepareProgram_totalQueryCost_le (N q size : Nat) (hsize : 0 < size) :
    totalQueryCost q (prepareProgram N q size) ≤ 760 * queryWork q size :=
  PA17QueryPrepare013.program_totalQueryCost_le N q size _ _ _ hsize

end PaperProofs.Structure.LaminarTree.PA17QueryLayout014
