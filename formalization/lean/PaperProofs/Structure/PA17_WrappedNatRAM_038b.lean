module
public import PaperProofs.Structure.PA17_WrappedNatRAM_038a

/-! Genuine finite-word certificates for the three wrapped actual bodies.
Arbitrary incoming query scratch words retain only the original Fits premise. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17WrappedNatRAM038b

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022 PA17PackedTranslator034 PA17DataFrame039
open PA17WrappedNatRAM038a

def bound (N q : Nat) : Nat := PA17QueryBudgetWord032.bound N q

theorem twice_bound (N q : Nat) : 2 * bound N q = 65536 * (N + q + 2) ^ 3 := PA17QueryBudgetWord032.twice_bound N q

theorem full_heap_bound (q : Nat) (full : List (Finset (Fin q))) :
    heapWords full.length q (prepareNormalization q full).indexed.nodes.size ≤ bound full.length q := by
  have hh := PA17QueryFootprint025.heapWords_le_cube full.length q _ (prepared_indexed_size_le q full)
  have hp := (PA17QueryFootprint025.powers_dominate full.length q).1
  unfold heapWords spillBase spillWords bound PA17QueryBudgetWord032.bound
  omega

theorem rolling_heap_bound (q : Nat) (full : List (Finset (Fin q))) :
    rollingHeapWords q (prepareNormalization q full).indexed.nodes.size ≤ bound full.length q := by
  have hs := PA17Implementation030.node_size_pos q full
  have hheap := PA17Rolling018B.heapWords_le q (prepareNormalization q full).indexed.nodes.size hs
  have hqwork := PA17QueryFootprint025.queryWork_le_cube full.length q _ (prepared_indexed_size_le q full)
  have hp := (PA17QueryFootprint025.powers_dominate full.length q).1
  unfold rollingHeapWords rollingSpillBase PA17GivenWord031f.heapWords spillWords bound PA17QueryBudgetWord032.bound
  nlinarith

theorem build_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * bound full.length q) (heapWords full.length q size) (givenTreeROM q full)
      (implementation.buildProgram full.length q size) (initial (fun _ => 0)) := by
  intro size
  have hb := PA17FullBuildWord036c.prepared_program_numeric q full hq hlaminar
  rw [← twice_bound full.length q] at hb
  have hpre := numericSafe_dataEq (2 * bound full.length q) (spillBase full.length q size) (givenTreeROM q full)
    (PA17TableBuild005.buildProgram full.length q size) _ _
    (wipe_initial_zero_dataEq (givenTreeROM q full).semantic (spillBase full.length q size)) hb
  apply logicalProgram_numeric (bound full.length q) (heapWords full.length q size) (spillBase full.length q size)
    (givenTreeROM q full) (PA17TableBuild005.buildProgram full.length q size) (full_heap_bound q full) le_rfl _ (fun _ => Nat.zero_le _)
  exact numericSafe_mono _ _ _ (by unfold heapWords; omega) _ _ _ hpre

theorem query_pre_table (q : Nat) (full : List (Finset (Fin q))) (rom : ROM) (heap : Nat → Nat)
    (htable : PhysicalTableCorrect q full heap) :
    PhysicalTableCorrect q full
      (execute rom (wipe (spillBase full.length q (prepareNormalization q full).indexed.nodes.size)) (initial heap)).heap := by
  apply PA17RequestPaths016.physicalTableCorrect_of_frame q full heap _ htable
  intro address ha
  apply wipe_frame rom _ _ address (Or.inl _)
  have hc := PA17CellLayout003.table_le_capacityWords full.length q (prepareNormalization q full).indexed.nodes.size
  change tableWords full.length q (prepareNormalization q full).indexed.nodes.size ≤
    PA17QueryLayout014.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size at hc
  have hcap : PA17QueryLayout014.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size ≤
      spillBase full.length q (prepareNormalization q full).indexed.nodes.size := Nat.le_add_right _ _
  omega

theorem query_pre_capacity (q : Nat) (full : List (Finset (Fin q))) (rom : PhysicalROM) (heap : Nat → Nat)
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size) heap) :
    CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size)
      (execute rom.semantic (wipe (spillBase full.length q (prepareNormalization q full).indexed.nodes.size)) (initial heap)).heap := by
  have hh := wipe_capacityThroughout q (PA17QueryLayout014.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size)
    (spillBase full.length q (prepareNormalization q full).indexed.nodes.size) rom (Nat.le_add_right _ _) (initial heap) hcap
    (wipe (spillBase full.length q (prepareNormalization q full).indexed.nodes.size)).length le_rfl
  simpa only [List.take_length] using hh

theorem query_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (heap : Nat → Nat)
    (htable : PhysicalTableCorrect q full heap)
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size) heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * bound full.length q) (heapWords full.length q size) (queryROM q full stage.val used)
      (implementation.queryProgram full.length q size) (initial heap) := by
  intro size
  let input := queryROM q full stage.val used
  have hw := wipe_numeric (bound full.length q) (heapWords full.length q size) (spillBase full.length q size) input
    (full_heap_bound q full) le_rfl (initial heap) (fun _ => Nat.zero_le _)
  have hb := PA17QueryWord033.prepared_program_numeric q full hq hlaminar stage used _
    (query_pre_table q full input.semantic heap htable) (query_pre_capacity q full input heap hcap) (hw.final _ _ _ _ _)
  apply logicalProgram_numeric (bound full.length q) (heapWords full.length q size) (spillBase full.length q size) input
    (PA17Query019.program full.length q size) (full_heap_bound q full) le_rfl (initial heap) (fun _ => Nat.zero_le _)
  have hwords : PA17QueryLayout014.heapWords full.length q size ≤ heapWords full.length q size := Nat.le_add_right _ _
  exact numericSafe_mono _ _ _ hwords _ _ _ hb

theorem rolling_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * bound full.length q) (rollingHeapWords q size) (queryROM q full 0 used)
      (implementation.rollingProgram full.length q size) (initial (fun _ => 0)) := by
  intro size
  have hb := PA17GivenWord031g.prepared_program_numeric q full hq hlaminar used
    (PA17GivenWord031g.numericBound full.length q) (PA17GivenWord031g.prepared_layout q full hq hlaminar used)
  have hpre := numericSafe_dataEq (2 * bound full.length q) (rollingSpillBase q size) (queryROM q full 0 used)
    (PA17Rolling018B.program full.length q size) _ _
    (wipe_initial_zero_dataEq (queryROM q full 0 used).semantic (rollingSpillBase q size)) hb
  apply logicalProgram_numeric (bound full.length q) (rollingHeapWords q size) (rollingSpillBase q size)
    (queryROM q full 0 used) (PA17Rolling018B.program full.length q size) (rolling_heap_bound q full) le_rfl _ (fun _ => Nat.zero_le _)
  exact numericSafe_mono _ _ _ (by unfold rollingHeapWords; omega) _ _ _ hpre

theorem build_footprint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    (givenTreeROM q full).size + heapWords full.length q size + (haltingWords (implementation.buildProgram full.length q size)).length ≤
      65536 * (full.length + q + 2) ^ 3 := by
  intro size
  have hc := PA17Implementation030.prepared_build_totalCost q full hq hlaminar
  have hw := PA17GivenWord031g.work_le_cube full.length q size (prepared_indexed_size_le q full)
  have hp := (PA17QueryFootprint025.powers_dominate full.length q).1
  change totalBuildCost (givenTreeROM q full) (PA17TableBuild005.buildProgram full.length q size) (spillBase full.length q size) ≤
    32768 * work full.length q size at hc
  unfold totalBuildCost at hc
  change (givenTreeROM q full).size + (spillBase full.length q size + spillWords) +
    (haltingWords (logicalProgram _ _)).length ≤ _
  rw [logicalProgram_code_length]
  simp only [spillWords]
  nlinarith

theorem query_footprint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    (queryROM q full stage.val used).size + heapWords full.length q size + (haltingWords (implementation.queryProgram full.length q size)).length ≤
      65536 * (full.length + q + 2) ^ 3 := by
  intro size
  have ht := prepared_indexed_size_le q full
  have hh := PA17QueryFootprint025.heapWords_le_cube full.length q size ht
  have hr := PA17QueryFootprint025.queryROM_size_le_cube q full hq hlaminar stage.val used
  have hc := PA17QueryFootprint025.query_code_length_le full.length q size (PA17Implementation030.node_size_pos q full)
  have hw := PA17QueryFootprint025.queryWork_le_cube full.length q size ht
  have hp := (PA17QueryFootprint025.powers_dominate full.length q).1
  change (queryROM q full stage.val used).size + (PA17QueryLayout014.heapWords full.length q size + spillWords) +
    (haltingWords (logicalProgram _ _)).length ≤ _
  rw [logicalProgram_code_length]
  simp only [spillWords]
  nlinarith

theorem rolling_footprint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    (queryROM q full 0 used).size + rollingHeapWords q size + (haltingWords (implementation.rollingProgram full.length q size)).length ≤
      65536 * (full.length + q + 2) ^ 3 := by
  intro size
  have hf := PA17GivenWord031g.prepared_footprint q full hq hlaminar used
  have hp := (PA17QueryFootprint025.powers_dominate full.length q).1
  change (queryROM q full 0 used).size + (PA17GivenWord031f.heapWords q size + spillWords) +
    (haltingWords (logicalProgram _ _)).length ≤ _
  rw [logicalProgram_code_length]
  simp only [spillWords]
  nlinarith

theorem build_execution (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ExecutionClaims 32 full.length q (heapWords full.length q size) (givenTreeROM q full)
      (implementation.buildProgram full.length q size) (initial (fun _ => 0)) := by
  intro size
  have hn := build_numeric q full hq hlaminar
  apply PA17WordBounds023.executionClaims_of_numeric_prefix full.length q _ _ _ (initial (fun _ => 0)) rfl
    (PA17WordBounds023.givenTreeROM_wordsFit q full) (build_footprint q full hq hlaminar)
    (by intro address _; exact pow_pos (by decide) _)
  · intro count hc register
    simpa only [twice_bound] using hn.1 count hc register
  · exact hn.2

theorem query_execution (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (heap : Nat → Nat)
    (htable : PhysicalTableCorrect q full heap)
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size) heap)
    (hfits : ∀ address < heapWords full.length q (prepareNormalization q full).indexed.nodes.size,
      Fits (indexWidth 32 full.length q) (heap address)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ExecutionClaims 32 full.length q (heapWords full.length q size) (queryROM q full stage.val used)
      (implementation.queryProgram full.length q size) (initial heap) := by
  intro size
  have hn := query_numeric q full hq hlaminar stage used heap htable hcap
  apply PA17WordBounds023.executionClaims_of_numeric_prefix full.length q _ _ _ (initial heap) rfl
    (PA17WordBounds023.queryROM_wordsFit q full stage used) (query_footprint q full hq hlaminar stage used) hfits
  · intro count hc register
    simpa only [twice_bound] using hn.1 count hc register
  · exact hn.2

theorem rolling_execution (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ExecutionClaims 32 full.length q (rollingHeapWords q size) (queryROM q full 0 used)
      (implementation.rollingProgram full.length q size) (initial (fun _ => 0)) := by
  intro size
  have hn := rolling_numeric q full hq hlaminar used
  apply PA17WordBounds023.executionClaims_of_numeric_prefix full.length q _ _ _ (initial (fun _ => 0)) rfl
    (PA17WordBounds023.queryROM_wordsFit q full ⟨0, by omega⟩ used) (rolling_footprint q full hq hlaminar used)
    (by intro address _; exact pow_pos (by decide) _)
  · intro count hc register
    simpa only [twice_bound] using hn.1 count hc register
  · exact hn.2

end PaperProofs.Structure.LaminarTree.PA17WrappedNatRAM038b
