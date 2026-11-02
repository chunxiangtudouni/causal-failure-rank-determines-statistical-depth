module
public import PaperProofs.Structure.PA17_WrappedNatRAM_038b

/-! Complete original NatRAM claims for the final three spill-wrapped bodies.
No incoming query scratch correctness or small-numeric oracle is added. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17WrappedNatRAM038c

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17PackedTranslator034 PA17DataFrame039
open PA17WrappedNatRAM038a PA17WrappedNatRAM038b

theorem build_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    tableWords N q size ≤ implementation.capacityWords N q size ∧
      implementation.capacityWords N q size * CapacityBits.width q ≤ constant * work N q size * Nat.clog 2 (q + 2) ∧
      implementation.indexWords N q size ≤ constant * (N + q + size + 1) ∧
      totalBuildCost (givenTreeROM q full) (implementation.buildProgram N q size) (heapWords N q size) ≤ constant * work N q size := by
  intro N size
  have hold := PA17Implementation030.prepared_build_resources q full hq hlaminar
  have hwork := (PA17Rolling018.dimension_le_work N q size (PA17Implementation030.node_size_pos q full)).2.2
  refine ⟨hold.1, ?_, ?_, ?_⟩
  · exact hold.2.1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show PA17Implementation030.constant ≤ constant by decide)))
  · change PA17QueryLayout014.indexWords N q size + 7 ≤ 65536 * (N + q + size + 1)
    have hh := PA17QueryLayout014.indexWords_le N q size
    omega
  · change totalBuildCost (givenTreeROM q full) (logicalProgram _ _) (_ + spillWords) ≤ 65536 * work N q size
    rw [logicalProgram_buildCost]
    have hc : totalBuildCost (givenTreeROM q full) (PA17TableBuild005.buildProgram N q size) (spillBase N q size) ≤
      32768 * work N q size := hold.2.2.2
    nlinarith

theorem build_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let body := implementation.buildProgram full.length q size
    PhysicalTableCorrect q full (execute (givenTreeROM q full).semantic body (initial (fun _ => 0))).heap ∧
      CapacityThroughout q (implementation.capacityWords full.length q size) (givenTreeROM q full) body (initial (fun _ => 0)) := by
  intro size body
  have hold := PA17Implementation030.prepared_build_correct q full hq hlaminar
  have hcap : implementation.capacityWords full.length q size ≤ spillBase full.length q size := Nat.le_add_right _ _
  have htable : tableWords full.length q size ≤ spillBase full.length q size :=
    (PA17CellLayout003.table_le_capacityWords full.length q size).trans hcap
  constructor
  · apply PA17RequestPaths016.physicalTableCorrect_of_frame q full _ _ hold.1
    intro address ha
    exact logicalProgram_zero_heap _ _ _ address (ha.trans_le htable)
  · apply logicalProgram_capacityThroughout q _ _ _ _ hcap (initial (fun _ => 0)) (fun _ _ => Nat.zero_le _)
    exact capacityThroughout_dataEq q _ _ _ _ _ (wipe_initial_zero_dataEq (givenTreeROM q full).semantic _) hold.2

theorem query_cost (q : Nat) (full : List (Finset (Fin q))) :
    let size := (prepareNormalization q full).indexed.nodes.size
    totalQueryCost q (implementation.queryProgram full.length q size) ≤ constant * queryWork q size := by
  intro size
  have hc := PA17Implementation030.prepared_query_cost q full
  have hp : 0 < queryWork q size := Nat.mul_pos (by omega) (PA17Implementation030.node_size_pos q full)
  change totalQueryCost q (logicalProgram _ _) ≤ 65536 * queryWork q size
  rw [logicalProgram_queryCost]
  change totalQueryCost q (PA17Query019.program full.length q size) ≤ 32768 * queryWork q size at hc
  nlinarith

theorem query_claims (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (heap : Nat → Nat) (htable : PhysicalTableCorrect q full heap)
    (hcap : CapacityPrefixBounded q (implementation.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size) heap)
    (hfits : ∀ address < heapWords full.length q (prepareNormalization q full).indexed.nodes.size,
      Fits (indexWidth 32 full.length q) (heap address)) (stage : Fin (full.length + 1)) (used : Finset (Fin q)) :
    QueryClaims constant 32 implementation q full hq (prepareNormalization q full).indexed.nodes.size
      (implementation.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size)
      (heapWords full.length q (prepareNormalization q full).indexed.nodes.size) stage used heap := by
  let size := (prepareNormalization q full).indexed.nodes.size
  let input := queryROM q full stage.val used
  let pre := execute input.semantic (wipe (spillBase full.length q size)) (initial heap)
  have hpretable := query_pre_table q full input.semantic heap htable
  have hprecap := query_pre_capacity q full input heap hcap
  have hcapbase : implementation.capacityWords full.length q size ≤ spillBase full.length q size := Nat.le_add_right _ _
  have htablebase : tableWords full.length q size ≤ spillBase full.length q size :=
    (PA17CellLayout003.table_le_capacityWords full.length q size).trans hcapbase
  refine ⟨query_cost q full, query_execution q full hq hlaminar stage used heap htable hcap hfits, ?_, ?_, ?_⟩
  · exact logicalProgram_replyCorrect q _ input.semantic _ (initial heap) _
      (PA17Query019.prepared_program_correct q full hq hlaminar stage used pre hpretable)
  · intro address ha
    have hf := PA17Query019.program_table_take_frame input.semantic full.length q size
      (PA17Query019.program full.length q size).length pre address ha
    rw [List.take_length] at hf
    dsimp only [pre] at hf
    change (execute input.semantic (logicalProgram (spillBase full.length q size) (PA17Query019.program full.length q size))
      (initial heap)).heap address = heap address
    rw [logicalProgram_execute, wipe_frame input.semantic _ _ address (Or.inl (ha.trans_le htablebase)), hf,
      wipe_frame input.semantic _ _ address (Or.inl (ha.trans_le htablebase))]
    rfl
  · exact logicalProgram_capacityThroughout q _ _ input _ hcapbase (initial heap) hcap
      (PA17Query019.program_capacityThroughout input full.length q size pre hprecap)

theorem rolling_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (used : Finset (Fin q)) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    let cap := implementation.rollingCapacityWords N q size
    2 * (q + 2) * (size + 1) ≤ cap ∧
      cap * CapacityBits.width q ≤ constant * queryWork q size * Nat.clog 2 (q + 2) ∧
      implementation.rollingIndexWords N q size ≤ constant * (q + size + 1) ∧
      totalBuildCost (queryROM q full 0 used) (implementation.rollingProgram N q size) (rollingHeapWords q size) ≤ constant * work N q size := by
  intro N size cap
  have hold := PA17Implementation030.prepared_rolling_resources q full hq hlaminar used
  have hwork := (PA17Rolling018.dimension_le_work N q size (PA17Implementation030.node_size_pos q full)).2.2
  refine ⟨hold.1, ?_, ?_, ?_⟩
  · exact hold.2.1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show PA17Implementation030.constant ≤ constant by decide)))
  · change PA17Rolling018B.indexWords q size + 7 ≤ 65536 * (q + size + 1)
    have hh := PA17Rolling018B.indexWords_le q size
    omega
  · change totalBuildCost (queryROM q full 0 used) (logicalProgram _ _) (_ + spillWords) ≤ 65536 * work N q size
    rw [logicalProgram_buildCost]
    have hc : totalBuildCost (queryROM q full 0 used) (PA17Rolling018B.program N q size) (rollingSpillBase q size) ≤
      32768 * work N q size := hold.2.2.2
    nlinarith

theorem rolling_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let input := queryROM q full 0 used
    let code := implementation.rollingProgram full.length q size
    let result := execute input.semantic code (initial (fun _ => 0))
    CapacityThroughout q (implementation.rollingCapacityWords full.length q size) input code (initial (fun _ => 0)) ∧
      result.register .value = encodeRank q (errorRank full (Finset.univ \ used)) ∧
      ∀ budget : Fin (q + 2), readEntry size budget.val result.heap =
        (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget := by
  intro size input code result
  have hold := PA17Implementation030.prepared_rolling_correct q full hq hlaminar used
  have hcap : implementation.rollingCapacityWords full.length q size ≤ rollingSpillBase q size := Nat.le_add_right _ _
  have htable : tableWords 0 q size ≤ rollingSpillBase q size := by
    have hh : (q + 2) * (size + 1) ≤ PA17Rolling018.workBase q size := by
      unfold PA17Rolling018.workBase
      rw [Nat.mul_assoc]
      omega
    simp only [tableWords, cells, Nat.zero_add, Nat.one_mul]
    unfold rollingSpillBase PA17GivenWord031f.heapWords PA17Rolling018.capacityWords
    omega
  refine ⟨?_, ?_, ?_⟩
  · apply logicalProgram_capacityThroughout q _ _ input _ hcap (initial (fun _ => 0)) (fun _ _ => Nat.zero_le _)
    exact capacityThroughout_dataEq q _ input _ _ _ (wipe_initial_zero_dataEq input.semantic _) hold.1
  · change (execute input.semantic (logicalProgram (rollingSpillBase q size) (PA17Rolling018B.program full.length q size))
      (initial (fun _ => 0))).register .value = _
    rw [logicalProgram_zero_register input.semantic _ _ .value (by decide) (by decide)]
    exact hold.2.1
  · intro budget
    rw [PA17RequestPaths016.readEntry_of_table_frame 0 q size budget.val
      (by simpa only [cells, Nat.zero_add, Nat.one_mul] using budget.isLt) _ _ (by
        intro address ha
        exact logicalProgram_zero_heap input.semantic _ _ address (ha.trans_le htable))]
    exact hold.2.2 budget

theorem implementation_claims : NatRAMImplementationClaims constant 32 implementation := by
  intro q full hq hlaminar
  let N := full.length
  let size := (prepareNormalization q full).indexed.nodes.size
  let cap := implementation.capacityWords N q size
  let words := heapWords N q size
  let build := implementation.buildProgram N q size
  let built := execute (givenTreeROM q full).semantic build (initial (fun _ => 0))
  have hb := build_execution q full hq hlaminar
  change ExecutionClaims 32 N q words (givenTreeROM q full) build (initial (fun _ => 0)) at hb
  have hr := build_resources q full hq hlaminar
  have hc := build_correct q full hq hlaminar
  have hqueries : ∀ heap : Nat → Nat, PhysicalTableCorrect q full heap → CapacityPrefixBounded q cap heap →
      (∀ address < words, Fits (indexWidth 32 N q) (heap address)) →
      ∀ stage : Fin (N + 1), ∀ used : Finset (Fin q), QueryClaims constant 32 implementation q full hq size cap words stage used heap := by
    intro heap htable hcap hfits stage used
    exact query_claims q full hq hlaminar heap htable hcap hfits stage used
  have hcapacity : CapacityPrefixBounded q cap built.heap := by
    have hbc : CapacityThroughout q cap (givenTreeROM q full) build (initial (fun _ => 0)) := hc.2
    have hh := hbc build.length le_rfl
    simpa only [List.take_length] using hh
  have hfits : ∀ address < words, Fits (indexWidth 32 N q) (built.heap address) := by
    have hh := hb.1.2.2.2.1 build.length le_rfl
    rw [List.take_length] at hh
    exact hh.2.2
  refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hb, hc.1, hc.2, hqueries, ?_, ?_⟩
  · dsimp only
    intro used
    have hrr := rolling_resources q full hq hlaminar used
    have hrc := rolling_correct q full hq hlaminar used
    exact ⟨hrr.1, hrr.2.1, hrr.2.2.1, hrr.2.2.2, rolling_execution q full hq hlaminar used, hrc.1, hrc.2⟩
  · intro requests hrequests
    exact PA17RequestPaths016.bounded_requests_claims constant 32 implementation q full hq cap words hqueries requests hrequests built.heap
      ⟨hc.1, hcapacity, hfits⟩

theorem fullNatRAMClaims : FullNatRAMClaims :=
  ⟨constant, 32, implementation, constant_pos, by decide, implementation_claims⟩

end PaperProofs.Structure.LaminarTree.PA17WrappedNatRAM038c
