module

public import PaperProofs.Structure.PA17_PackedPhase_045d

/-! The three actual packed programs and original-input body certificates. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedPhase045

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM PA17PackedTranslator034
open PA17QueryHeaderWord022 PA17DataFrame039

def programs : PackedPrograms where
  build := fun N q size => packedProgram q (indexWidth 32 N q)
    (PA17QueryLayout014.capacityWords N q size) (PA17QueryLayout014.indexWords N q size)
    (PA17TableBuild005.buildProgram N q size)
  query := fun N q size => packedProgram q (indexWidth 32 N q)
    (PA17QueryLayout014.capacityWords N q size) (PA17QueryLayout014.indexWords N q size)
    (PA17Query019.program N q size)
  rolling := fun N q size => packedProgram q (indexWidth 32 N q)
    (PA17Rolling018.capacityWords q size) (PA17Rolling018B.indexWords q size)
    (PA17Rolling018B.program N q size)

theorem unpackHeap_zero (q capWords bits : Nat) :
    unpackHeap q capWords bits (fun _ => BitVec.ofNat bits 0) = fun _ => 0 := by
  have hz (width : Nat) : CapacityBits.decodeScalar (List.replicate width false) = 0 := by
    unfold CapacityBits.decodeScalar
    have hb : BitVec.ofBoolListLE (List.replicate width false) = BitVec.ofNat _ 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro index
      simp
    rw [hb]
    rfl
  funext address
  unfold unpackHeap
  split_ifs
  · simpa only [BitVec.getLsbD_zero, List.ofFn_const] using hz (CapacityBits.width q)
  · rfl

theorem prewipe_registers_zero (rom : ROM) (base : Nat) (heap : Nat → Nat) :
    ∀ register, (execute rom (wipe base) (initial heap)).register register = 0 := by
  intro register
  rw [wipe_register]
  split_ifs <;> rfl

theorem full_index_le (q : Nat) (full : List (Finset (Fin q))) :
    PA17QueryLayout014.indexWords full.length q (prepareNormalization q full).indexed.nodes.size ≤
      36 * (full.length + q + 2) ^ 3 := by
  have hh := PA17QueryFootprint025.heapWords_le_cube full.length q _ (prepared_indexed_size_le q full)
  unfold PA17QueryLayout014.heapWords at hh
  omega

theorem full_capacity_pos (N q size : Nat) : 0 < PA17QueryLayout014.capacityWords N q size := by
  unfold PA17QueryLayout014.capacityWords PA17CellLayout003.capacityWords
  omega

theorem rolling_capacity_le (q : Nat) (full : List (Finset (Fin q))) :
    PA17Rolling018.capacityWords q (prepareNormalization q full).indexed.nodes.size ≤
      36 * (full.length + q + 2) ^ 3 := by
  have hh := PA17Rolling018B.heapWords_le q (prepareNormalization q full).indexed.nodes.size
    (PA17Implementation030.node_size_pos q full)
  have hw := PA17QueryFootprint025.queryWork_le_cube full.length q _ (prepared_indexed_size_le q full)
  nlinarith

theorem rolling_index_le (q : Nat) (full : List (Finset (Fin q))) :
    PA17Rolling018B.indexWords q (prepareNormalization q full).indexed.nodes.size ≤
      36 * (full.length + q + 2) ^ 3 := by
  have hh := PA17Rolling018B.indexWords_le q (prepareNormalization q full).indexed.nodes.size
  have ht := prepared_indexed_size_le q full
  have hp := PA17QueryFootprint025.powers_dominate full.length q
  nlinarith

theorem build_body_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let cap := PA17QueryLayout014.capacityWords full.length q size
    let indices := PA17QueryLayout014.indexWords full.length q size
    NumericSafe (65536 * (full.length + q + 2) ^ 3) (cap + indices) (givenTreeROM q full)
      (PA17TableBuild005.buildProgram full.length q size)
      (execute (givenTreeROM q full).semantic (wipe (cap + indices))
        (initial (unpackHeap q cap (indexWidth 32 full.length q) (fun _ => BitVec.ofNat _ 0)))) := by
  intro size cap indices
  rw [unpackHeap_zero]
  exact numericSafe_dataEq _ _ _ _ _ _
    (PA17WrappedNatRAM038a.wipe_initial_zero_dataEq (givenTreeROM q full).semantic (cap + indices))
    (PA17FullBuildWord036c.prepared_program_numeric q full hq hlaminar)

theorem query_body_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q))
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (htable : PhysicalTableCorrect q full (unpackHeap q (PA17QueryLayout014.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size) (indexWidth 32 full.length q) heap))
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size)
      (unpackHeap q (PA17QueryLayout014.capacityWords full.length q
        (prepareNormalization q full).indexed.nodes.size) (indexWidth 32 full.length q) heap)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let cap := PA17QueryLayout014.capacityWords full.length q size
    let indices := PA17QueryLayout014.indexWords full.length q size
    NumericSafe (65536 * (full.length + q + 2) ^ 3) (cap + indices) (queryROM q full stage.val used)
      (PA17Query019.program full.length q size)
      (execute (queryROM q full stage.val used).semantic (wipe (cap + indices))
        (initial (unpackHeap q cap (indexWidth 32 full.length q) heap))) := by
  intro size cap indices
  rw [← PA17QueryBudgetWord032.twice_bound]
  apply PA17QueryWord033.prepared_program_numeric q full hq hlaminar stage used
  · exact PA17WrappedNatRAM038b.query_pre_table q full _ _ htable
  · exact PA17WrappedNatRAM038b.query_pre_capacity q full _ _ hcap
  · intro register
    rw [prewipe_registers_zero]
    exact Nat.zero_le _

theorem rolling_body_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let cap := PA17Rolling018.capacityWords q size
    let indices := PA17Rolling018B.indexWords q size
    NumericSafe (65536 * (full.length + q + 2) ^ 3) (cap + indices) (queryROM q full 0 used)
      (PA17Rolling018B.program full.length q size)
      (execute (queryROM q full 0 used).semantic (wipe (cap + indices))
        (initial (unpackHeap q cap (indexWidth 32 full.length q) (fun _ => BitVec.ofNat _ 0)))) := by
  intro size cap indices
  rw [unpackHeap_zero, ← PA17GivenWord031g.twice_numericBound]
  exact numericSafe_dataEq _ _ _ _ _ _
    (PA17WrappedNatRAM038a.wipe_initial_zero_dataEq (queryROM q full 0 used).semantic (cap + indices))
    (PA17GivenWord031g.prepared_program_numeric q full hq hlaminar used _ (PA17GivenWord031g.prepared_layout q full hq hlaminar used))

end PaperProofs.Structure.LaminarTree.PA17PackedPhase045
