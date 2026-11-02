module

public import PaperProofs.Structure.PA17_BuildCapacity_007
public import PaperProofs.Structure.PA17_BuildResources_006
public import PaperProofs.Structure.PA17_QueryFootprint_025
public import PaperProofs.Structure.PA17_Rolling_018C
public import PaperProofs.Structure.PA17_RequestPaths_016

/-! One concrete implementation, with all three actual programs. The
semantic and resource results below do not assert the still-open finite
word, physical packing or uniform generator obligations. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17Implementation030

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def implementation : Implementation where
  buildProgram := PA17TableBuild005.buildProgram
  queryProgram := PA17Query019.program
  rollingProgram := PA17Rolling018B.program
  capacityWords := PA17QueryLayout014.capacityWords
  indexWords := PA17QueryLayout014.indexWords
  rollingCapacityWords := fun _ q size => PA17Rolling018.capacityWords q size
  rollingIndexWords := fun _ q size => PA17Rolling018B.indexWords q size

def constant : Nat := 32768

theorem constant_pos : 0 < constant := by decide

theorem node_size_pos (q : Nat) (full : List (Finset (Fin q))) :
    0 < (prepareNormalization q full).indexed.nodes.size := by
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt

theorem heapWords_le_work (N q size : Nat) (hsize : 0 < size) :
    PA17QueryLayout014.heapWords N q size ≤ 40 * work N q size := by
  have hd := PA17BuildResources006.dimension_le_work N q size hsize
  have hc := PA17BuildResources006.capacityWords_le N q size hsize
  dsimp only [PA17QueryLayout014.heapWords, PA17QueryLayout014.capacityWords,
    PA17QueryLayout014.indexWords]
  omega

/-- Loading includes the larger workspace reused by the actual query. -/
theorem prepared_build_totalCost (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    totalBuildCost (givenTreeROM q full) (implementation.buildProgram full.length q size)
      (implementation.capacityWords full.length q size + implementation.indexWords full.length q size) ≤
        constant * work full.length q size := by
  intro size
  have hs := node_size_pos q full
  have ht := PA17TableBuild005.buildProgram_trace_le full.length q size hs
  have hl := PA17BuildResources006.program_length_le_trace (PA17TableBuild005.buildProgram full.length q size)
  have hr := PA17BuildResources006.givenTreeROM_size_le q full hq hlaminar
  have hh := heapWords_le_work full.length q size hs
  have hw := (PA17BuildResources006.dimension_le_work full.length q size hs).2.2
  change totalBuildCost (givenTreeROM q full) (PA17TableBuild005.buildProgram full.length q size)
    (PA17QueryLayout014.heapWords full.length q size) ≤ constant * work full.length q size
  rw [totalBuildCost, haltingWords_length, List.length_append, haltTrace_length]
  rw [List.length_append, haltTrace_length] at ht
  dsimp only [constant]
  nlinarith

theorem prepared_build_resources (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    tableWords N q size ≤ implementation.capacityWords N q size ∧
      implementation.capacityWords N q size * CapacityBits.width q ≤
        constant * work N q size * Nat.clog 2 (q + 2) ∧
      implementation.indexWords N q size ≤ constant * (N + q + size + 1) ∧
      totalBuildCost (givenTreeROM q full) (implementation.buildProgram N q size)
        (implementation.capacityWords N q size + implementation.indexWords N q size) ≤
          constant * work N q size := by
  intro N size
  refine ⟨PA17CellLayout003.table_le_capacityWords N q size, ?_, ?_,
    prepared_build_totalCost q full hq hlaminar⟩
  · exact (PA17BuildResources006.capacity_bits_le N q size (node_size_pos q full)).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show 8 ≤ constant by decide)))
  · exact (PA17QueryLayout014.indexWords_le N q size).trans
      (Nat.mul_le_mul_right _ (show 24 ≤ constant by decide))

theorem prepared_build_correct (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    PhysicalTableCorrect q full (execute (givenTreeROM q full).semantic
      (implementation.buildProgram full.length q size) (initial (fun _ => 0))).heap ∧
    CapacityThroughout q (implementation.capacityWords full.length q size) (givenTreeROM q full)
      (implementation.buildProgram full.length q size) (initial (fun _ => 0)) :=
  ⟨(PA17TableBuild005.prepared_build_correct q full hq hlaminar).1,
    PA17BuildCapacity007.prepared_build_capacityThroughout q full hq hlaminar⟩

theorem prepared_query_cost (q : Nat) (full : List (Finset (Fin q))) :
    let size := (prepareNormalization q full).indexed.nodes.size
    totalQueryCost q (implementation.queryProgram full.length q size) ≤ constant * queryWork q size := by
  intro size
  exact (PA17Query019.totalQueryCost_le full.length q size (node_size_pos q full)).trans
    (Nat.mul_le_mul_right _ (show 16384 ≤ constant by decide))

/-- Only the original execution certificate remains a premise here. All
answer, cost, table and capacity fields come from the actual query proof. -/
theorem queryClaims_of_execution (wordFactor q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (heap : Nat → Nat) (htable : PhysicalTableCorrect q full heap)
    (hcapacity : CapacityPrefixBounded q (implementation.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size) heap)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q))
    (hexecution : ExecutionClaims wordFactor full.length q
      (PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size)
      (queryROM q full stage.val used)
      (implementation.queryProgram full.length q (prepareNormalization q full).indexed.nodes.size)
      (initial heap)) :
    QueryClaims constant wordFactor implementation q full hq (prepareNormalization q full).indexed.nodes.size
      (implementation.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size)
      (PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size)
      stage used heap := by
  refine ⟨prepared_query_cost q full, hexecution,
    PA17Query019.prepared_program_correct q full hq hlaminar stage used (initial heap) htable, ?_,
    PA17Query019.program_capacityThroughout (queryROM q full stage.val used) full.length q _ (initial heap) hcapacity⟩
  intro address ha
  change (execute (queryROM q full stage.val used).semantic
    (PA17Query019.program full.length q (prepareNormalization q full).indexed.nodes.size)
    (initial heap)).heap address = (initial heap).heap address
  simpa only [List.take_length] using PA17Query019.program_table_take_frame
    (queryROM q full stage.val used).semantic full.length q _
    (PA17Query019.program full.length q (prepareNormalization q full).indexed.nodes.size).length
    (initial heap) address ha

theorem prepared_rolling_resources (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    let cap := implementation.rollingCapacityWords N q size
    2 * (q + 2) * (size + 1) ≤ cap ∧
      cap * CapacityBits.width q ≤ constant * queryWork q size * Nat.clog 2 (q + 2) ∧
      implementation.rollingIndexWords N q size ≤ constant * (q + size + 1) ∧
      totalBuildCost (queryROM q full 0 used) (implementation.rollingProgram N q size)
        (cap + implementation.rollingIndexWords N q size) ≤ constant * work N q size := by
  intro N size cap
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [cap, implementation, PA17Rolling018.capacityWords, PA17Rolling018.workBase]
    omega
  · exact (PA17Rolling018.capacity_bits_le q size (node_size_pos q full)).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show 12 ≤ constant by decide)))
  · exact (PA17Rolling018B.indexWords_le q size).trans
      (Nat.mul_le_mul_right _ (show 7 ≤ constant by decide))
  · exact (PA17Rolling018B.prepared_program_totalCost q full hq hlaminar used).trans
      (Nat.mul_le_mul_right _ (show 16000 ≤ constant by decide))

theorem prepared_rolling_correct (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    let input := queryROM q full 0 used
    let result := execute input.semantic (implementation.rollingProgram N q size) (initial (fun _ => 0))
    CapacityThroughout q (implementation.rollingCapacityWords N q size) input
      (implementation.rollingProgram N q size) (initial (fun _ => 0)) ∧
      result.register .value = encodeRank q (errorRank full (Finset.univ \ used)) ∧
      ∀ budget : Fin (q + 2), readEntry size budget.val result.heap =
        (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget :=
  ⟨PA17Rolling018C.prepared_program_capacityThroughout q full hq hlaminar used,
    PA17Rolling018B.prepared_program_semantics q full hq hlaminar used⟩

/-- Assembly at the original quantifiers. This is deliberately conditional
on the three remaining execution-certificate families, rather than an A17
completion claim. Arbitrary request reuse requires no new premise. -/
theorem natRAM_of_execution (wordFactor : Nat)
    (hbuild : ∀ (q : Nat) (full : List (Finset (Fin q))), 0 < q → LaminarSchedule full →
      let size := (prepareNormalization q full).indexed.nodes.size
      ExecutionClaims wordFactor full.length q (PA17QueryLayout014.heapWords full.length q size)
        (givenTreeROM q full) (implementation.buildProgram full.length q size) (initial (fun _ => 0)))
    (hquery : ∀ (q : Nat) (full : List (Finset (Fin q))), 0 < q → LaminarSchedule full →
      let size := (prepareNormalization q full).indexed.nodes.size
      ∀ heap : Nat → Nat, PhysicalTableCorrect q full heap →
        CapacityPrefixBounded q (implementation.capacityWords full.length q size) heap →
        (∀ address < PA17QueryLayout014.heapWords full.length q size,
          Fits (indexWidth wordFactor full.length q) (heap address)) →
        ∀ stage : Fin (full.length + 1), ∀ used : Finset (Fin q),
        ExecutionClaims wordFactor full.length q (PA17QueryLayout014.heapWords full.length q size)
          (queryROM q full stage.val used) (implementation.queryProgram full.length q size) (initial heap))
    (hrolling : ∀ (q : Nat) (full : List (Finset (Fin q))), 0 < q → LaminarSchedule full →
      let size := (prepareNormalization q full).indexed.nodes.size
      ∀ used : Finset (Fin q),
      ExecutionClaims wordFactor full.length q
        (implementation.rollingCapacityWords full.length q size + implementation.rollingIndexWords full.length q size)
        (queryROM q full 0 used) (implementation.rollingProgram full.length q size) (initial (fun _ => 0))) :
    NatRAMImplementationClaims constant wordFactor implementation := by
  intro q full hq hlaminar
  let size := (prepareNormalization q full).indexed.nodes.size
  let cap := implementation.capacityWords full.length q size
  let heapWords := PA17QueryLayout014.heapWords full.length q size
  let build := implementation.buildProgram full.length q size
  let built := execute (givenTreeROM q full).semantic build (initial (fun _ => 0))
  have hb := hbuild q full hq hlaminar
  have hr := prepared_build_resources q full hq hlaminar
  have hc := prepared_build_correct q full hq hlaminar
  have hqueries : ∀ heap : Nat → Nat, PhysicalTableCorrect q full heap →
      CapacityPrefixBounded q cap heap →
      (∀ address < heapWords, Fits (indexWidth wordFactor full.length q) (heap address)) →
      ∀ stage : Fin (full.length + 1), ∀ used : Finset (Fin q),
      QueryClaims constant wordFactor implementation q full hq size cap heapWords stage used heap := by
    intro heap htable hcapacity hfits stage used
    exact queryClaims_of_execution wordFactor q full hq hlaminar heap htable hcapacity stage used
      (hquery q full hq hlaminar heap htable hcapacity hfits stage used)
  have hcapacity : CapacityPrefixBounded q cap built.heap := by
    have hf := hc.2 (implementation.buildProgram full.length q
      (prepareNormalization q full).indexed.nodes.size).length le_rfl
    rw [List.take_length] at hf
    exact hf
  have hfits : ∀ address < heapWords, Fits (indexWidth wordFactor full.length q) (built.heap address) := by
    have hfinal := hb.1.2.2.2.1 build.length le_rfl
    rw [List.take_length] at hfinal
    exact hfinal.2.2
  refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hb, hc.1, hc.2, hqueries, ?_, ?_⟩
  · dsimp only
    intro used
    have hrr := prepared_rolling_resources q full hq hlaminar used
    have hrc := prepared_rolling_correct q full hq hlaminar used
    exact ⟨hrr.1, hrr.2.1, hrr.2.2.1, hrr.2.2.2,
      hrolling q full hq hlaminar used, hrc.1, hrc.2⟩
  · intro requests hrequests
    exact PA17RequestPaths016.bounded_requests_claims constant wordFactor implementation q full hq cap heapWords
      hqueries requests hrequests built.heap ⟨hc.1, hcapacity, hfits⟩

end PaperProofs.Structure.LaminarTree.PA17Implementation030
