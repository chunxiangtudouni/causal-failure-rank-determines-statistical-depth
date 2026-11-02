module

public import PaperProofs.Structure.PA17_CellLayout_003
public import PaperProofs.Structure.PA17_MetadataAssembly_003
public import PaperProofs.Structure.PA17_TableBuild_005
public import PaperProofs.Structure.RawTreeSerialization

/-! Loading and allocation bounds for the concrete given-tree build layout.
These are resource arithmetic, not a replacement for prefix word safety. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17BuildResources006

open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem dimension_le_work (N q size : Nat) (hsize : 0 < size) :
    N + q + 1 ≤ work N q size ∧ size ≤ work N q size ∧ 1 ≤ work N q size := by
  have hbase : N + q + 1 ≤ (N + 1) * (q + 1) := by nlinarith
  have hb : 1 ≤ (N + 1) * (q + 1) := by nlinarith
  have ht := Nat.mul_le_mul_left ((N + 1) * (q + 1)) hsize
  have hs := Nat.mul_le_mul_right size hb
  simp only [Nat.mul_one, Nat.one_mul] at ht hs
  exact ⟨hbase.trans ht, hs, hb.trans ht⟩

theorem capacityWords_le (N q size : Nat) (hsize : 0 < size) :
    PA17CellLayout003.capacityWords N q size ≤ 8 * work N q size := by
  exact PA17MetadataAssembly003.capacityWords_le N q size hsize

theorem capacity_bits_le (N q size : Nat) (hsize : 0 < size) :
    PA17CellLayout003.capacityWords N q size * CapacityBits.width q ≤
      8 * work N q size * Nat.clog 2 (q + 2) := by
  have hw : CapacityBits.width q ≤ Nat.clog 2 (q + 2) :=
    Nat.clog_mono_right 2 (by omega)
  exact Nat.mul_le_mul (capacityWords_le N q size hsize) hw

def indexWords (N size : Nat) : Nat := PA17MetadataAssembly003.indexWords N size
def heapWords (N q size : Nat) : Nat := PA17CellLayout003.capacityWords N q size + indexWords N size

theorem indexWords_le_linear (N q size : Nat) : indexWords N size ≤ 3 * (N + q + size + 1) :=
  PA17MetadataAssembly003.indexWords_le N q size

theorem indexWords_le_work (N q size : Nat) (hsize : 0 < size) : indexWords N size ≤ 4 * work N q size := by
  have hh := dimension_le_work N q size hsize
  dsimp [indexWords, PA17MetadataAssembly003.indexWords]
  omega

theorem heapWords_le (N q size : Nat) (hsize : 0 < size) : heapWords N q size ≤ 12 * work N q size := by
  have hc := capacityWords_le N q size hsize
  have hi := indexWords_le_work N q size hsize
  dsimp [heapWords]
  omega

theorem givenTreeROM_size_le (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    (givenTreeROM q full).size ≤ 8 * work full.length q (prepareNormalization q full).indexed.nodes.size := by
  let N := full.length
  let size := (prepareNormalization q full).indexed.nodes.size
  have hsize : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have hh := dimension_le_work N q size hsize
  have hNq : N * q ≤ work N q size := by
    have hb : N * q ≤ (N + 1) * (q + 1) := by nlinarith
    exact hb.trans (Nat.le_mul_of_pos_right _ hsize)
  have hqt : q * size ≤ work N q size := by
    have hb : q ≤ (N + 1) * (q + 1) := by nlinarith
    exact Nat.mul_le_mul_right size hb
  rw [PhysicalROM.size, RawTreeSerialization.givenTreeROM_input_length,
    RawTreeSerialization.givenTreeROM_internal_length,
    RawTreeSerialization.givenTreeROM_children_length q full hq hlaminar]
  change 3 + N * q + size * q + 2 * size + (size - 1) ≤ 8 * work N q size
  have hs : size - 1 ≤ size := Nat.sub_le _ _
  rw [Nat.mul_comm size q]
  omega

theorem program_length_le_trace (program : List Op) : program.length ≤ (trace program).length := by
  have ho (op : Op) : 1 ≤ op.trace.length := by
    cases op with
    | subtract target left right => exact Nat.zero_lt_succ _
    | base instruction => cases instruction <;> exact Nat.zero_lt_succ _
  induction program with
  | nil => exact Nat.zero_le _
  | cons op later ih =>
    rw [List.length_cons, trace, List.flatMap_cons, List.length_append]
    have hh := ho op
    change later.length + 1 ≤ op.trace.length + (trace later).length
    omega

theorem build_loading_cost_le (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (program : List Op) (constant : Nat)
    (htrace : (trace program).length ≤ constant * work full.length q (prepareNormalization q full).indexed.nodes.size) :
    totalBuildCost (givenTreeROM q full) program
      (heapWords full.length q (prepareNormalization q full).indexed.nodes.size) ≤
      (6 * constant + 39) * work full.length q (prepareNormalization q full).indexed.nodes.size := by
  let N := full.length
  let size := (prepareNormalization q full).indexed.nodes.size
  have hsize : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have hr := givenTreeROM_size_le q full hq hlaminar
  have hh := heapWords_le N q size hsize
  have hp := program_length_le_trace program
  have hw := (dimension_le_work N q size hsize).2.2
  rw [totalBuildCost, haltingWords_length, List.length_append, haltTrace_length]
  change _ ≤ (6 * constant + 39) * work N q size
  change (trace program).length ≤ constant * work N q size at htrace
  change (givenTreeROM q full).size ≤ 8 * work N q size at hr
  nlinarith

theorem prepared_build_totalCost (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    totalBuildCost (givenTreeROM q full) (PA17TableBuild005.buildProgram full.length q size)
      (heapWords full.length q size) ≤ 7059 * work full.length q size := by
  intro size
  have hsize : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have ht := PA17TableBuild005.buildProgram_trace_le full.length q size hsize
  rw [List.length_append, haltTrace_length] at ht
  apply build_loading_cost_le q full hq hlaminar _ 1170
  change (trace (PA17TableBuild005.buildProgram full.length q size)).length ≤ 1170 * work full.length q size
  omega

theorem prepared_build_resources (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    tableWords N q size ≤ PA17CellLayout003.capacityWords N q size ∧
      PA17CellLayout003.capacityWords N q size * CapacityBits.width q ≤
        7059 * work N q size * Nat.clog 2 (q + 2) ∧
      indexWords N size ≤ 7059 * (N + q + size + 1) ∧
      totalBuildCost (givenTreeROM q full) (PA17TableBuild005.buildProgram N q size)
        (heapWords N q size) ≤ 7059 * work N q size := by
  intro N size
  have hsize : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  refine ⟨PA17CellLayout003.table_le_capacityWords N q size, ?_, ?_, prepared_build_totalCost q full hq hlaminar⟩
  · exact (capacity_bits_le N q size hsize).trans (by gcongr; decide)
  · exact (indexWords_le_linear N q size).trans (Nat.mul_le_mul_right _ (by decide))

end PaperProofs.Structure.LaminarTree.PA17BuildResources006
