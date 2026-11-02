module

public import Structure.PA06_A19Prepare_Completion060_Program
public import Structure.PA06_A19Prepare_Completion060_Header
public import Structure.PA06_A19Prepare_Completion060_CanonicalPrefix
public import Structure.PA06_A19Prepare_PostDP055_Data
public import Structure.PA06_A19Prepare_FinalRepresentation059_MetadataFrameActual
public import Structure.PA06_A19Prepare_FinalRepresentation057_UsedFrameActual
public import Structure.PSTR_BuildLower_TableEndpoint_125

set_option autoImplicit false
set_option warningAsError true

/-! One actual532 clock, followed by the real135 used loop and24 header.
The table comes from the SAME actual post-DP Prepared endpoint via frozen125.
There is no table/metadata answer or whole-run hSafe caller premise.
This suffix does not assert safety of the earlier fullBuild AST.
Candidate until strict validation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompletion060

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims
open PA06A19PreparePreBuild044 (bits capacity allocation)
open PA06A19PrepareInitialUsed037 (Fetched)

theorem postDP_table (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (before : WordState (bits q full))
    (data : PA06A19PreparePostDP055.Data q full before) :
    PhysicalTableCorrect q full (logicalHeap q (capacity q full) before.heap) := by
  have table := PSTRBuildLower.SourceRep.table_endpoint q full hq hl before data.source
  simpa only [PA06A19PreparePreBuild044.capacity, PSTRBuildLower.PreparedLayout.capacity,
    PSTRBuildLower.PreparedLayout.t, treeSize, Nat.ne_of_gt hq, ite_false] using table

theorem postDP_logical_bounded (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (before : WordState (bits q full))
    (data : PA06A19PreparePostDP055.Data q full before) :
    CapacityPrefixBounded q (capacity q full) (logicalHeap q (capacity q full) before.heap) := by
  simpa only [logicalHeap, ite_eq_right (Nat.ne_of_gt hq)] using data.capacityBounded

theorem suffix_run (left : List PackingOp) (q : Nat) (full : List (Finset (Fin q)))
    (used : Finset (Fin q)) (hq : 0 < q) (hl : LaminarSchedule full)
    (before : WordState (bits q full)) (data : PA06A19PreparePostDP055.Data q full before)
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (program left)))
    (hcodePC : Fits (bits q full) (5 * (program left).length)) :
    ∃ metadataClock ≤ PA06A19PrepareStaticMetadata036.metadataNatBound full.length q
        (PA06A19PrepareChildrenCache023.preparedSize q full),
      let clock := metadataClock + PA06A19PrepareInitialUsed037.clock q + 24
      let rom := controllerInput q full used
      let after := packingRun rom (program left) clock before
      HeapRepresents q full (capacity q full) ⟨0, used, false⟩ after.heap ∧
      after.halted = false ∧ after.pc.toNat = 5 * (program left).length ∧
      after.register .address = before.register .address ∧
      ∀ count < clock, Fetched (allocation q full) rom (program left)
        (packingRun rom (program left) count before) := by
  let rom := controllerInput q full used
  let code := program left
  have metaCode : WordsFit (bits q full)
      (packingCode (left ++ PA06A19PrepareStaticMetadata036.metadataProgramAt left.length ++
        metadataRight left.length)) := by rw [metadata_layout]; exact hcode
  have metaCodePC : Fits (bits q full)
      (5 * (left ++ PA06A19PrepareStaticMetadata036.metadataProgramAt left.length ++
        metadataRight left.length).length) := by rw [metadata_layout]; exact hcodePC
  obtain ⟨metadataClock, metadataBound, metaPost⟩ :=
    PA06A19PrepareFinalRepresentation059.actual_metadata_resources left (metadataRight left.length)
      q full used hq hl before data.scan data.children hpc ha metaCode metaCodePC
  dsimp only at metaPost
  rw [metadata_layout] at metaPost
  rcases metaPost with ⟨_words, metaValues, _addresses, _capacityEq, metaTableTransfer,
    metaBoundTransfer, metaDataTransfer, metaHeaderTransfer, metaAddress, metaPC, metaActive,
    _metaFrame, metaPrefixes⟩
  let middle := packingRun rom code metadataClock before
  have middleData := metaDataTransfer data.scalars
  have middleHeader := metaHeaderTransfer data.header
  have middleTable := metaTableTransfer (postDP_table q full hq hl before data)
  have middleBound := metaBoundTransfer (postDP_logical_bounded q full hq before data)
  have usedCode : WordsFit (bits q full)
      (packingCode (usedLeft left ++ PA06A19PrepareInitialUsed037.programAt (usedLeft left).length ++
        PA06A19PrepareFinalHeader033.program)) := by rw [used_layout]; exact hcode
  have usedCodePC : Fits (bits q full)
      (5 * (usedLeft left ++ PA06A19PrepareInitialUsed037.programAt (usedLeft left).length ++
        PA06A19PrepareFinalHeader033.program).length) := by rw [used_layout]; exact hcodePC
  have middlePC : middle.pc.toNat = 5 * (usedLeft left).length := by
    rw [usedLeft_length]
    exact metaPC
  have usedPost := PA06A19PrepareFinalRepresentation057.actual_initialUsed_resources q full used hq hl
    (usedLeft left) PA06A19PrepareFinalHeader033.program middle middlePC metaActive middleData
    middleHeader middleBound usedCode usedCodePC
  dsimp only at usedPost
  rw [used_layout] at usedPost
  rcases usedPost with ⟨_current, _storedData, headerBank, storedHeader, storedBound, storedUsed,
    storedTableTransfer, _storedPhysicalMetadata, storedMetadata, storedActive, storedPC, storedAddress⟩
  let stored := packingRun rom code (PA06A19PrepareInitialUsed037.clock q) middle
  have storedTable := storedTableTransfer middleTable
  have storedValues (position : Nat) (hp : position < (staticMetadata q full).length) :
      logicalHeap q (capacity q full) stored.heap (capacity q full + 2 + position) =
        (staticMetadata q full)[position]'hp :=
    (storedMetadata position hp).trans (metaValues position hp)
  have storedPC' : stored.pc.toNat = 5 * (headerLeft left).length := by
    rw [headerLeft_length]
    rw [usedLeft_length] at storedPC
    omega
  have headerCode : WordsFit (bits q full)
      (packingCode (headerLeft left ++ PA06A19PrepareFinalHeader033.program ++ [])) := by
    rw [header_layout]
    exact hcode
  have headerCodePC : Fits (bits q full)
      (5 * (headerLeft left ++ PA06A19PrepareFinalHeader033.program ++ []).length) := by
    rw [header_layout]
    exact hcodePC
  have represents := actual_header_represents q full used hq hl (headerLeft left) [] stored
    storedPC' storedActive headerBank storedHeader storedTable storedValues storedUsed storedBound
    headerCode headerCodePC
  rw [header_layout] at represents
  have control := PA06A19PrepareFinalHeader033.actual_control q full used hq (headerLeft left) [] stored
    storedPC' storedActive headerBank storedHeader headerCode headerCodePC
  dsimp only at control
  rw [header_layout] at control
  have metaFetched (count : Nat) (hc : count < metadataClock) :
      Fetched (allocation q full) rom code (packingRun rom code count before) := by
    obtain ⟨_address, active, pc, op, decoded, access⟩ := metaPrefixes count hc
    exact ⟨active, pc, op, decoded, by
      simpa only [PA06A19PreparePreBuild044.children_allocation q full hq] using access⟩
  have middleUnpacked : CapacityPrefixBounded q (capacity q full)
      (unpackHeap q (capacity q full) (bits q full) (dataHeap middle.heap)) := by
    simpa only [logicalHeap, ite_eq_right (Nat.ne_of_gt hq)] using middleBound
  have usedFetched (count : Nat) (hc : count < PA06A19PrepareInitialUsed037.clock q) :
      Fetched (allocation q full) rom code (packingRun rom code count middle) := by
    have actual := PA06A19PrepareInitialUsed037.actual_initialUsed_prefix q full used hq
      (usedLeft left) PA06A19PrepareFinalHeader033.program middle middlePC metaActive
      middleData.bank037 middleHeader middleUnpacked usedCode usedCodePC count hc
    rw [used_layout] at actual
    exact actual
  have headerFetched (count : Nat) (hc : count < 24) :
      Fetched (allocation q full) rom code (packingRun rom code count stored) := by
    have actual := PA06A19PrepareFinalHeader033.actual_prefix_access q full used hq (headerLeft left) []
      stored storedPC' storedActive headerBank storedHeader headerCode headerCodePC count hc
    dsimp only at actual
    rw [header_layout] at actual
    exact actual
  have storedRun : packingRun rom code
      (metadataClock + PA06A19PrepareInitialUsed037.clock q) before = stored :=
    PA06A19PrepareRawHeader039Body.wordRun_add rom code metadataClock
      (PA06A19PrepareInitialUsed037.clock q) before
  have firstPrefixes := PA06A19PrepareCompletion060Canonical.fetched_add (allocation q full) rom code before metadataClock
    (PA06A19PrepareInitialUsed037.clock q) metaFetched usedFetched
  have prefixes := PA06A19PrepareCompletion060Canonical.fetched_add (allocation q full) rom code before
    (metadataClock + PA06A19PrepareInitialUsed037.clock q) 24 firstPrefixes (by
      intro count hc
      rw [storedRun]
      exact headerFetched count hc)
  have finalRun : packingRun rom code
      (metadataClock + PA06A19PrepareInitialUsed037.clock q + 24) before =
        packingRun rom code 24 stored := by
    rw [PA06A19PrepareRawHeader039Body.wordRun_add, storedRun]
  refine ⟨metadataClock, metadataBound, ?_⟩
  dsimp only
  rw [finalRun]
  refine ⟨represents, control.1, ?_, control.2.2.trans (storedAddress.trans metaAddress), ?_⟩
  · rw [program_length]
    have finalPC : (packingRun rom code 24 stored).pc.toNat = 5 * ((headerLeft left).length + 24) :=
      control.2.1
    rw [headerLeft_length] at finalPC
    omega
  · exact prefixes

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompletion060
