module

public import Structure.PA06_A19Prepare_FinalRepresentation056_HeaderFrame
public import Structure.PA06_A19Prepare_InitialUsed037_Bounds
public import Structure.PA06_A19Prepare_PreBuild044_Layout

set_option autoImplicit false
set_option warningAsError true

/-! The real24-op header turns prior actual table/metadata/used results
into the original HeapRepresents. These are internal segment inputs,
delivered by the preceding running producers, not raw caller premises.
Candidate until strict validation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompletion060

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims
open PA06A19PreparePreBuild044 (bits capacity)

theorem actual_header_represents (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (left right : List PackingOp)
    (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (bank : PA06A19PrepareFinalHeader033.BankData q full before)
    (header : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (table : PhysicalTableCorrect q full (logicalHeap q (capacity q full) before.heap))
    (metadata : ∀ position (hp : position < (staticMetadata q full).length),
      logicalHeap q (capacity q full) before.heap (capacity q full + 2 + position) =
        (staticMetadata q full)[position]'hp)
    (usedBits : ∀ tool : Fin q,
      logicalHeap q (capacity q full) before.heap
          (tableWords full.length q (treeSize q full) + tool.val) = bit (decide (tool ∈ used)))
    (bounded : CapacityPrefixBounded q (capacity q full) (logicalHeap q (capacity q full) before.heap))
    (hcode : WordsFit (indexWidth 32 full.length q)
      (packingCode (left ++ PA06A19PrepareFinalHeader033.program ++ right)))
    (hcodePC : Fits (indexWidth 32 full.length q)
      (5 * (left ++ PA06A19PrepareFinalHeader033.program ++ right).length)) :
    HeapRepresents q full (capacity q full) ⟨0, used, false⟩
      (packingRun (controllerInput q full used)
        (left ++ PA06A19PrepareFinalHeader033.program ++ right) 24 before).heap := by
  let after := packingRun (controllerInput q full used)
    (left ++ PA06A19PrepareFinalHeader033.program ++ right) 24 before
  have live := PA06A19PrepareFinalHeader033.actual_liveFields q full used hq left right before
    hpc ha bank header hcode hcodePC
  have frame := PA06A19PrepareFinalRepresentation056.actual_header_logical_frame q full used hq hl
    left right before hpc ha bank header hcode hcodePC
  have tableBound : tableWords full.length q (treeSize q full) ≤ capacity q full :=
    (PA06A19PreparePackedView013.tableWords_le_oldCapacity full.length q (treeSize q full)).trans
      (PA06A19PreparePackedView013.oldCapacity_le_capacity full.length q (treeSize q full) hq)
  have afterTable : PhysicalTableCorrect q full (logicalHeap q (capacity q full) after.heap) := by
    apply (PA06A19PreparePackedView013.physicalTableCorrect_congr_prefix q full _ _ ?_).mpr table
    intro address ha'
    have ha : address < tableWords full.length q (treeSize q full) := by
      simpa only [treeSize, Nat.ne_of_gt hq, ite_false] using ha'
    exact frame.1 address (ha.trans_le tableBound)
  have afterBound : CapacityPrefixBounded q (capacity q full)
      (logicalHeap q (capacity q full) after.heap) := by
    intro address ha'
    rw [frame.1 address ha']
    exact bounded address ha'
  refine ⟨live.1, live.2.1, live.2.2.1, live.2.2.2.1,
    live.2.2.2.2.1, live.2.2.2.2.2, ?_, ?_, ?_⟩
  · intro position hp
    exact (frame.2 position hp).trans (metadata position hp)
  · intro tool
    have ht : tableWords full.length q (treeSize q full) + tool.val < capacity q full :=
      PA06A19PrepareInitialUsed037.pointer_lt_capacity full.length q (treeSize q full) tool.val hq tool.isLt
    exact (frame.1 _ ht).trans (usedBits tool)
  · intro _positive
    exact ⟨afterTable, afterBound⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompletion060
