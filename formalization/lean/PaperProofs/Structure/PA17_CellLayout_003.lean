module

public import PaperProofs.Structure.PA17_UniformCell_002

/-! A concrete persistent layout for the dimension-only cell kernel.
All table/work/accumulator capacities precede every index/metadata word.
This is a layout component, not a completed Implementation. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17CellLayout003

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17TagBridge001

def workBase (N q size : Nat) : Nat := tableWords N q size
def accumulatorBase (N q size : Nat) : Nat := workBase N q size + size + 1
def capacityWords (N q size : Nat) : Nat := workBase N q size + 2 * (size + 1)
def metadataBase (N q size : Nat) : Nat := capacityWords N q size
def stageBase (N q size : Nat) : Nat := metadataBase N q size + 3 * size + 1

theorem table_slot_bound (N q size slot : Nat) (hslot : slot < cells N q)
    (index : Nat) (hi : index ≤ size) : slot * (size + 1) + index < tableWords N q size := by
  have hh := Nat.mul_le_mul_right (size + 1) (show slot + 1 ≤ cells N q from by omega)
  rw [Nat.add_mul, Nat.one_mul] at hh
  unfold tableWords
  omega

theorem table_le_capacityWords (N q size : Nat) : tableWords N q size ≤ capacityWords N q size := by
  dsimp [capacityWords, workBase]
  omega

theorem work_good_disjoint (N q size slot : Nat) (hslot : slot < cells N q) :
    DisjointSlots size (workBase N q size) (slot * (size + 1)) := by
  intro left _ right hr
  have hb := table_slot_bound N q size slot hslot right hr
  dsimp [workBase]
  omega

theorem work_accumulator_disjoint (N q size : Nat) :
    DisjointSlots size (workBase N q size) (accumulatorBase N q size) := by
  intro left hl right _
  dsimp [accumulatorBase]
  omega

theorem good_accumulator_disjoint (N q size slot : Nat) (hslot : slot < cells N q) :
    DisjointSlots size (slot * (size + 1)) (accumulatorBase N q size) := by
  intro left hl right _
  have hb := table_slot_bound N q size slot hslot left hl
  dsimp [accumulatorBase, workBase]
  omega

theorem capacity_slots_before_indices (N q size index : Nat) (hi : index ≤ size) :
    workBase N q size + index < metadataBase N q size ∧
      accumulatorBase N q size + index < metadataBase N q size := by
  dsimp [accumulatorBase, metadataBase, capacityWords]
  omega

theorem work_parent_disjoint (N q size index : Nat) (hi : index < size)
    (encoded : Nat) (_he : encoded ≤ size) :
    workBase N q size + index ≠ metadataBase N q size + size + encoded := by
  have hb := (capacity_slots_before_indices N q size index (by omega)).1
  omega

def kernelProgram (N q size goodSlot stage : Nat) : List Op :=
  PA17UniformCell002.kernelProgram size (workBase N q size) (goodSlot * (size + 1))
    (accumulatorBase N q size) (metadataBase N q size + size) (stageBase N q size + stage)

theorem prepared_kernelProgram_result (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (goodSlot : Nat)
    (hslot : goodSlot < cells full.length q) (stage : Fin full.length)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (state : State)
    (hmetadata : UniformTreeMetadataRAM.MetadataCorrect q full
      (metadataBase full.length q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hstage : state.heap (stageBase full.length q (prepareNormalization q full).indexed.nodes.size + stage.val) =
      encodedNode (prepareNormalization q full).indexed (IndexedQuery.storedStageNode q full hq stage))
    (hg : TagFirstRep (prepareNormalization q full).indexed state.heap
      (goodSlot * ((prepareNormalization q full).indexed.nodes.size + 1)) good)
    (hb : IndexedCellRAM.SlotRep (prepareNormalization q full).indexed state.heap
      (workBase full.length q (prepareNormalization q full).indexed.nodes.size) bad) :
    let cache := (prepareNormalization q full).indexed
    IndexedCellRAM.SlotRep cache (execute (givenTreeROM q full).semantic
      (kernelProgram full.length q cache.nodes.size goodSlot stage.val) state).heap
      (workBase full.length q cache.nodes.size) (IndexedEntry.cell cache full[stage.val] good bad) := by
  exact PA17UniformCell002.prepared_kernelProgram_result q full hq hlaminar _ _ _ _ _
    (work_good_disjoint _ _ _ _ hslot) (work_accumulator_disjoint _ _ _)
    (good_accumulator_disjoint _ _ _ _ hslot) (work_parent_disjoint _ _ _) stage good bad state hmetadata hstage hg hb

theorem prepared_kernelProgram_frame (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (goodSlot : Nat) (stage : Fin full.length)
    (state : State)
    (hmetadata : UniformTreeMetadataRAM.MetadataCorrect q full
      (metadataBase full.length q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hstage : state.heap (stageBase full.length q (prepareNormalization q full).indexed.nodes.size + stage.val) =
      encodedNode (prepareNormalization q full).indexed (IndexedQuery.storedStageNode q full hq stage))
    (address : Nat)
    (ha : address < tableWords full.length q (prepareNormalization q full).indexed.nodes.size ∨
      capacityWords full.length q (prepareNormalization q full).indexed.nodes.size ≤ address) :
    (execute (givenTreeROM q full).semantic
      (kernelProgram full.length q (prepareNormalization q full).indexed.nodes.size goodSlot stage.val) state).heap address = state.heap address := by
  let size := (prepareNormalization q full).indexed.nodes.size
  change address < tableWords full.length q size ∨ capacityWords full.length q size ≤ address at ha
  have hw (index : Nat) (hi : index ≤ size) : address ≠ workBase full.length q size + index := by
    have hb := (capacity_slots_before_indices full.length q size index hi).1
    dsimp [metadataBase] at hb
    rcases ha with ha | ha
    · dsimp [workBase]; omega
    · omega
  have hac (index : Nat) (hi : index ≤ size) : address ≠ accumulatorBase full.length q size + index := by
    have hb := (capacity_slots_before_indices full.length q size index hi).2
    dsimp [metadataBase] at hb
    rcases ha with ha | ha
    · dsimp [accumulatorBase, workBase]; omega
    · omega
  exact PA17UniformCell002.prepared_kernelProgram_frame q full hq hlaminar _ _ _ _ _
    (work_parent_disjoint _ _ _) stage state hmetadata hstage address hw hac

end PaperProofs.Structure.LaminarTree.PA17CellLayout003
