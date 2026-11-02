module

public import Structure.PA06_A19Prepare_FinalRepresentation057_UsedFrame

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED one real037 run plus its concrete logical/source frames.
Only actual lower-level permanent data, temporary header, full capacity
bound and code/PC facts enter this wrapper. Table/metadata are not inputs;
their source-to-output preservation is a proved conclusion. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalRepresentation057
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims
open PA06A19PreparePreBuild044 (bits capacity packedWords ScalarData)
open PA06A19PrepareInitialUsed037 (Current)

theorem actual_initialUsed_resources (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (left right : List PackingOp)
    (original : WordState (bits q full))
    (hpc : original.pc.toNat = 5 * left.length) (ha : original.halted = false)
    (data : ScalarData q full original)
    (header : PA06A19PrepareRuntimePacked016.Header q original.heap)
    (bounded : CapacityPrefixBounded q (capacity q full) (logicalHeap q (capacity q full) original.heap))
    (hcode : WordsFit (bits q full)
      (packingCode (left ++ PA06A19PrepareInitialUsed037.programAt left.length ++ right)))
    (hpcCode : Fits (bits q full)
      (5 * (left ++ PA06A19PrepareInitialUsed037.programAt left.length ++ right).length)) :
    let after := packingRun (controllerInput q full used)
      (left ++ PA06A19PrepareInitialUsed037.programAt left.length ++ right)
      (PA06A19PrepareInitialUsed037.clock q) original
    Current q full used original q after ∧
    ScalarData q full after ∧ PA06A19PrepareFinalHeader033.BankData q full after ∧
    PA06A19PrepareRuntimePacked016.Header q after.heap ∧
    CapacityPrefixBounded q (capacity q full) (logicalHeap q (capacity q full) after.heap) ∧
    (∀ tool : Fin q,
      logicalHeap q (capacity q full) after.heap (tableWords full.length q (treeSize q full) + tool.val) =
        bit (decide (tool ∈ used))) ∧
    (PhysicalTableCorrect q full (logicalHeap q (capacity q full) original.heap) →
      PhysicalTableCorrect q full (logicalHeap q (capacity q full) after.heap)) ∧
    (∀ position < (staticMetadata q full).length,
      after.heap (BitVec.ofNat (bits q full) (6 + packedWords q full + position)) =
        original.heap (BitVec.ofNat (bits q full) (6 + packedWords q full + position))) ∧
    (∀ position < (staticMetadata q full).length,
      logicalHeap q (capacity q full) after.heap (capacity q full + 2 + position) =
        logicalHeap q (capacity q full) original.heap (capacity q full + 2 + position)) ∧
    after.halted = false ∧ after.pc.toNat = 5 * (left.length + 135) ∧
    after.register .address = original.register .address := by
  have unpacked : CapacityPrefixBounded q (capacity q full)
      (unpackHeap q (capacity q full) (bits q full) (dataHeap original.heap)) := by
    simpa only [logicalHeap, ite_eq_right (Nat.ne_of_gt hq)] using bounded
  obtain ⟨current, active, pc, address⟩ :=
    PA06A19PrepareInitialUsed037.actual_initialUsed q full used hq left right original hpc ha
      data.bank037 header unpacked hcode hpcCode
  let after := packingRun (controllerInput q full used)
    (left ++ PA06A19PrepareInitialUsed037.programAt left.length ++ right)
    (PA06A19PrepareInitialUsed037.clock q) original
  have afterData : ScalarData q full after := current_scalarData q full used hq original after current data
  dsimp only
  refine ⟨current, afterData, scalarData_finalHeaderBank q full after afterData,
    current.header, current_logical_bounded q full used hq original after current,
    current_used_bits q full used hq original after current, ?_, ?_, ?_, active, pc, address⟩
  · exact current_table_correct q full used hq original after current
  · exact current_metadata_physical_frame q full used hq hl original after current data.bank037.base
  · exact current_metadata_logical_frame q full used hq hl original after current data.bank037.base

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalRepresentation057
