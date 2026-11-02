module

public import PaperProofs.Structure.PA17_PackedPhase_045e

/-! Original build, rolling, and arbitrary-physical-heap query phase targets.
All translator certificates are discharged by the actual original programs. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17PackedPhase045

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM PA17PackedTranslator034
open PA17QueryHeaderWord022 PA17DataFrame039

theorem build_phase (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    let impl := PA17WrappedNatRAM038a.implementation
    PackedPhaseRefines 512 32 N q size (impl.capacityWords N q size) (impl.indexWords N q size)
      (givenTreeROM q full) (impl.buildProgram N q size) (programs.build N q size) (fun _ => BitVec.ofNat _ 0) := by
  intro N size impl
  let cap := PA17QueryLayout014.capacityWords N q size
  let indices := PA17QueryLayout014.indexWords N q size
  let body := PA17TableBuild005.buildProgram N q size
  change PackedPhaseRefines 512 32 N q size cap (newIndexWords indices) (givenTreeROM q full)
    (logicalProgram (cap + indices) body) (packedProgram q (indexWidth 32 N q) cap indices body) _
  have hn := build_body_numeric q full hq hlaminar
  apply packedPhaseRefines 32 N q size cap indices body (givenTreeROM q full) _
    (PA17Implementation030.node_size_pos q full)
    (prepared_layout N q cap indices (full_capacity_pos N q size)
      (PA17PackingBounds043.fullCapacity_le q full) (full_index_le q full))
    (PA17WordBounds023.givenTreeROM_wordsFit q full)
  · apply packedFootprint_fit N q cap indices body (givenTreeROM q full)
      (PA17PackingBounds043.fullCapacity_le q full) (full_index_le q full)
    have hh := PA17WrappedNatRAM038b.build_footprint q full hq hlaminar
    change (givenTreeROM q full).size + PA17WrappedNatRAM038a.heapWords N q size +
      (haltingWords (logicalProgram (cap + indices) body)).length ≤ 65536 * (N + q + 2) ^ 3 at hh
    omega
  · intro count hc register
    exact PA17WordBounds023.cubic_fits N q _ (hn.1 count hc register)
  · exact hn.2
  · rw [unpackHeap_zero]
    exact capacityThroughout_dataEq q cap (givenTreeROM q full) body _ _
      (PA17WrappedNatRAM038a.wipe_initial_zero_dataEq (givenTreeROM q full).semantic (cap + indices))
      (PA17BuildCapacity007.prepared_build_capacityThroughout q full hq hlaminar)

theorem rolling_phase (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    let impl := PA17WrappedNatRAM038a.implementation
    PackedPhaseRefines 512 32 N q size (impl.rollingCapacityWords N q size) (impl.rollingIndexWords N q size)
      (queryROM q full 0 used) (impl.rollingProgram N q size) (programs.rolling N q size) (fun _ => BitVec.ofNat _ 0) := by
  intro N size impl
  let cap := PA17Rolling018.capacityWords q size
  let indices := PA17Rolling018B.indexWords q size
  let body := PA17Rolling018B.program N q size
  change PackedPhaseRefines 512 32 N q size cap (newIndexWords indices) (queryROM q full 0 used)
    (logicalProgram (cap + indices) body) (packedProgram q (indexWidth 32 N q) cap indices body) _
  have hn := rolling_body_numeric q full hq hlaminar used
  have hpos : 0 < cap := by unfold cap PA17Rolling018.capacityWords; omega
  apply packedPhaseRefines 32 N q size cap indices body (queryROM q full 0 used) _
    (PA17Implementation030.node_size_pos q full)
    (prepared_layout N q cap indices hpos (rolling_capacity_le q full) (rolling_index_le q full))
    (PA17WordBounds023.queryROM_wordsFit q full ⟨0, by omega⟩ used)
  · apply packedFootprint_fit N q cap indices body (queryROM q full 0 used)
      (rolling_capacity_le q full) (rolling_index_le q full)
    have hh := PA17WrappedNatRAM038b.rolling_footprint q full hq hlaminar used
    change (queryROM q full 0 used).size + PA17WrappedNatRAM038a.rollingHeapWords q size +
      (haltingWords (logicalProgram (cap + indices) body)).length ≤ 65536 * (N + q + 2) ^ 3 at hh
    omega
  · intro count hc register
    exact PA17WordBounds023.cubic_fits N q _ (hn.1 count hc register)
  · exact hn.2
  · rw [unpackHeap_zero]
    exact capacityThroughout_dataEq q cap (queryROM q full 0 used) body _ _
      (PA17WrappedNatRAM038a.wipe_initial_zero_dataEq (queryROM q full 0 used).semantic (cap + indices))
      (PA17Rolling018C.prepared_program_capacityThroughout q full hq hlaminar used)

theorem query_phase (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (htable : PhysicalTableCorrect q full (unpackHeap q (PA17QueryLayout014.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size) (indexWidth 32 full.length q) heap))
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size)
      (unpackHeap q (PA17QueryLayout014.capacityWords full.length q
        (prepareNormalization q full).indexed.nodes.size) (indexWidth 32 full.length q) heap))
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    let impl := PA17WrappedNatRAM038a.implementation
    PackedPhaseRefines 512 32 N q size (impl.capacityWords N q size) (impl.indexWords N q size)
      (queryROM q full stage.val used) (impl.queryProgram N q size) (programs.query N q size) heap := by
  intro N size impl
  let cap := PA17QueryLayout014.capacityWords N q size
  let indices := PA17QueryLayout014.indexWords N q size
  let body := PA17Query019.program N q size
  let rom := queryROM q full stage.val used
  let pre := execute rom.semantic (wipe (cap + indices)) (initial (unpackHeap q cap (indexWidth 32 N q) heap))
  change PackedPhaseRefines 512 32 N q size cap (newIndexWords indices) rom
    (logicalProgram (cap + indices) body) (packedProgram q (indexWidth 32 N q) cap indices body) heap
  have hn := query_body_numeric q full hq hlaminar stage used heap htable hcap
  apply packedPhaseRefines 32 N q size cap indices body rom heap
    (PA17Implementation030.node_size_pos q full)
    (prepared_layout N q cap indices (full_capacity_pos N q size)
      (PA17PackingBounds043.fullCapacity_le q full) (full_index_le q full))
    (PA17WordBounds023.queryROM_wordsFit q full stage used)
  · apply packedFootprint_fit N q cap indices body rom
      (PA17PackingBounds043.fullCapacity_le q full) (full_index_le q full)
    have hh := PA17WrappedNatRAM038b.query_footprint q full hq hlaminar stage used
    change rom.size + PA17WrappedNatRAM038a.heapWords N q size +
      (haltingWords (logicalProgram (cap + indices) body)).length ≤ 65536 * (N + q + 2) ^ 3 at hh
    omega
  · intro count hc register
    exact PA17WordBounds023.cubic_fits N q _ (hn.1 count hc register)
  · exact hn.2
  · exact PA17Query019.program_capacityThroughout rom N q size pre
      (PA17WrappedNatRAM038b.query_pre_capacity q full rom _ hcap)

theorem three_phases (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    let impl := PA17WrappedNatRAM038a.implementation
    let cap := impl.capacityWords N q size
    let indices := impl.indexWords N q size
    PackedPhaseRefines 512 32 N q size cap indices (givenTreeROM q full)
      (impl.buildProgram N q size) (programs.build N q size) (fun _ => BitVec.ofNat _ 0) ∧
    (∀ used : Finset (Fin q), PackedPhaseRefines 512 32 N q size
      (impl.rollingCapacityWords N q size) (impl.rollingIndexWords N q size) (queryROM q full 0 used)
      (impl.rollingProgram N q size) (programs.rolling N q size) (fun _ => BitVec.ofNat _ 0)) ∧
    ∀ heap : BitVec (indexWidth 32 N q) → BitVec (indexWidth 32 N q),
      PhysicalTableCorrect q full (unpackHeap q cap (indexWidth 32 N q) heap) →
      CapacityPrefixBounded q cap (unpackHeap q cap (indexWidth 32 N q) heap) →
      ∀ stage : Fin (N + 1), ∀ used : Finset (Fin q),
        PackedPhaseRefines 512 32 N q size cap indices (queryROM q full stage.val used)
          (impl.queryProgram N q size) (programs.query N q size) heap :=
  ⟨build_phase q full hq hlaminar, fun used => rolling_phase q full hq hlaminar used,
    fun heap htable hcap stage used => query_phase q full hq hlaminar heap htable hcap stage used⟩

end PaperProofs.Structure.LaminarTree.PA17PackedPhase045
