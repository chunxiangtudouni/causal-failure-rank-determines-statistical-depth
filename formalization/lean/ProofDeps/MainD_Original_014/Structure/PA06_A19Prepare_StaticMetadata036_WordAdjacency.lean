module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordAdjacencyChunks

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual all-clock safety of the same55-op adjacency producer. The
original common32 width and8192 allocation discharge every range/room
obligation. Its source is the real023 output; only actual code position,
permanent cells and arbitrary full-width registers are caller inputs.
The remaining477 static instructions and their loops are separate work. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass parentAddress degreeBase highCacheEnd actualPackedWords actualControlBase
    actualAllocation OutputData RunFacts mass_fits32)

/-- No all-run safety or future metadata table is assumed. Every source
word bound below is derived from the original cached parents/degrees/
children, and every target is before the actual runtime control bank. -/
theorem adjacency_actual_runFacts (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (rom : PhysicalROM)
    (left right : List PackingOp) (before : NatState)
    (output : OutputData q full (actualControlBase q full) before)
    (hpermanentT : before.heap (actualControlBase q full + 2) = preparedSize q full)
    (hpermanentBase : before.heap (actualControlBase q full + 6) = 4 + actualPackedWords q full)
    (hreg : RegistersFit (indexWidth 32 full.length q) before)
    (hpc : before.pc = 5 * left.length) (ha : before.halted = false)
    (hcodePC : Fits (indexWidth 32 full.length q)
      (5 * (left ++ adjacencyProgramAt left.length ++ right).length)) :
    RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
      rom (left ++ adjacencyProgramAt left.length ++ right) (adjacencyTotalSteps (preparedSize q full)) before := by
  let bits := indexWidth 32 full.length q
  let B := metadataWordLimit bits
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  let H := actualAllocation q full
  let t := preparedSize q full
  let M := mass q full
  let code := left ++ adjacencyProgramAt left.length ++ right
  have ht : 0 < t := by
    have h := PA06A19PrepareControlBank017.treeSize_pos full hq
    simpa only [treeSize, Nat.ne_of_gt hq, ite_false] using h
  have htM : t ≤ M := prepared_indexed_size_le q full
  have hlayout : CB = 4 + P + 4096 * (M + t) := rfl
  have hbelow : 6 + P + 3 * t ≤ CB := (adjacency_below_control M t P ht).trans_eq hlayout.symm
  have disjoint := adjacency_sources_disjoint CB M t P ht hlayout
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  change highCacheEnd CB M < H ∧ Fits bits H ∧ Fits bits (highCacheEnd CB M) at room
  have controlRoom : CB < H := by
    have h := room.1
    unfold highCacheEnd at h
    omega
  have heapBound : H ≤ B := metadata_le_wordLimit room.2.1
  have massBound : M ≤ B := metadata_le_wordLimit (mass_fits32 q full)
  have codeBound : 5 * code.length ≤ B := metadata_le_wordLimit hcodePC
  have regs : RegistersLE B before := fun reg => metadata_le_wordLimit (hreg reg)
  have ends := adjacency_source_ends q full CB
  change parentAddress CB M 0 + t ≤ highCacheEnd CB M ∧
    degreeBase CB M + (2 * t - 1) ≤ highCacheEnd CB M at ends
  have words := adjacency_source_words_le q full hq hl CB before output
  change (∀ index < t, before.heap (parentAddress CB M 0 + index) ≤ M) ∧
    (∀ index < 2 * t - 1, before.heap (degreeBase CB M + index) ≤ M) at words
  let seed := runOps rom initializeAdjacency before
  have initRun : natRun rom code 22 before = seed := initializeAdjacency_run rom left right before hpc ha
  have initSafe : RunFacts B H rom code 22 before :=
    initializeAdjacency_runFacts rom B H CB P M t left right before regs output.1.address
      output.1.mass_cell hpermanentT hpermanentBase htM hlayout room.1 heapBound hpc ha
  have seedRegs : RegistersLE B seed := by
    have h := ((initSafe.1).final _ _ _ _ _).1
    rw [initRun] at h
    exact h
  have seedEffect := initializeAdjacency_effect rom CB M t P before output.1.address
    output.1.mass_cell hpermanentT hpermanentBase (by omega)
  change seed.register .address = CB ∧ seed.register .index = parentAddress CB M 0 ∧
    seed.register .old = 7 + P ∧ seed.register .total = t ∧ seed.register .fresh = 1 ∧
    seed.register .flag = 0 ∧ seed.heap = Function.update before.heap (6 + P) (t - 1) at seedEffect
  rcases seedEffect with ⟨seedCB, seedIndex, seedOld, seedTotal, seedFresh, seedFlag, seedHeap⟩
  have seedPC : seed.pc = 5 * (left.length + 22) := by
    rw [runOps_pc rom _ before initializeAdjacency_noJump, hpc, initializeAdjacency_length]
    omega
  have seedActive : seed.halted = false := (runOps_halted rom _ before).trans ha
  have seedWords : ∀ index < t, seed.heap (parentAddress CB M 0 + index) ≤ B := by
    intro index hi
    rw [seedHeap, Function.update_of_ne (by unfold parentAddress; omega)]
    exact (words.1 index hi).trans massBound
  let first := natRun rom code (9 * t + 2) seed
  have firstSafeRaw := copy_runFacts rom B H (left ++ initializeAdjacency)
    (setupDegreeChildren ++ copyProgramAt (left.length + 46) ++ right)
    CB (parentAddress CB M 0) (7 + P) t seed
    (by simpa only [List.length_append, initializeAdjacency_length] using seedPC) seedActive
    seedRegs seedCB seedIndex seedOld seedTotal seedFresh seedFlag disjoint.1
    (ends.1.trans room.1.le) (by omega) heapBound seedWords
    (by simpa only [code, adjacencyProgramAt, List.length_append, initializeAdjacency_length,
      copyProgramAt_length, setupDegreeChildren_length, Nat.add_assoc] using codeBound)
  have firstSafe : RunFacts B H rom code (9 * t + 2) seed := by
    simpa only [code, adjacencyProgramAt, List.length_append, initializeAdjacency_length,
      List.append_assoc] using firstSafeRaw
  have firstRegs : RegistersLE B first := ((firstSafe.1).final _ _ _ _ _).1
  have firstDataRaw := copy_run rom (left ++ initializeAdjacency)
    (setupDegreeChildren ++ copyProgramAt (left.length + 46) ++ right)
    CB (parentAddress CB M 0) (7 + P) t seed
    (by simpa only [List.length_append, initializeAdjacency_length] using seedPC) seedActive
    seedCB seedIndex seedOld seedTotal seedFresh seedFlag disjoint.1
  have firstData : (∀ index < t, first.heap (7 + P + index) = seed.heap (parentAddress CB M 0 + index)) ∧
      (∀ address, address < 7 + P ∨ 7 + P + t ≤ address → first.heap address = seed.heap address) ∧
      first.register .address = CB ∧ first.register .old = 7 + P + t ∧
      first.register .fresh = 1 ∧ first.register .flag = 0 ∧
      first.pc = 5 * (left.length + 31) ∧ first.halted = false := by
    simpa only [first, code, adjacencyProgramAt, List.length_append, initializeAdjacency_length,
      copyProgramAt_length, List.append_assoc, Nat.add_assoc] using firstDataRaw
  rcases firstData with ⟨_firstWords, firstFrame, firstCB, firstOld, _firstFresh,
    firstFlag, firstPC, firstActive⟩
  have firstM : first.heap (CB + 528) = M := by
    rw [firstFrame _ (Or.inr (by omega)), seedHeap, Function.update_of_ne (by omega)]
    exact output.1.mass_cell
  have firstT : first.heap (CB + 2) = t := by
    rw [firstFrame _ (Or.inr (by omega)), seedHeap, Function.update_of_ne (by omega)]
    exact hpermanentT
  let setup := runOps rom setupDegreeChildren first
  have setupRun : natRun rom code 15 first = setup :=
    setupDegreeChildren_run rom left right first firstPC firstActive
  have setupSafe : RunFacts B H rom code 15 first :=
    setupDegreeChildren_runFacts rom B H CB M t left right first firstRegs firstCB firstM firstT
      htM room.1 heapBound firstPC firstActive
  have setupRegs : RegistersLE B setup := by
    have h := ((setupSafe.1).final _ _ _ _ _).1
    rw [setupRun] at h
    exact h
  have setupEffect := setupDegreeChildren_effect rom CB M t first firstCB firstM firstT
  change setup.register .address = CB ∧ setup.register .index = degreeBase CB M ∧
    setup.register .old = first.register .old ∧ setup.register .total = 2 * t - 1 ∧
    setup.register .fresh = 1 ∧ setup.register .flag = first.register .flag ∧ setup.heap = first.heap at setupEffect
  rcases setupEffect with ⟨setupCB, setupIndex, setupOld, setupTotal, setupFresh, setupFlag, setupHeap⟩
  have setupPC : setup.pc = 5 * (left.length + 46) := by
    rw [runOps_pc rom _ first setupDegreeChildren_noJump, firstPC, setupDegreeChildren_length]
    omega
  have setupActive : setup.halted = false := (runOps_halted rom _ first).trans firstActive
  have setupWords : ∀ index < 2 * t - 1, setup.heap (degreeBase CB M + index) ≤ B := by
    intro index hi
    rw [setupHeap, firstFrame _ (Or.inr (by unfold degreeBase; omega)), seedHeap,
      Function.update_of_ne (by unfold degreeBase; omega)]
    exact (words.2 index hi).trans massBound
  have lastSafeRaw := copy_runFacts rom B H
    (left ++ initializeAdjacency ++ copyProgramAt (left.length + 22) ++ setupDegreeChildren)
    right CB (degreeBase CB M) (7 + P + t) (2 * t - 1) setup
    (by simpa only [List.length_append, initializeAdjacency_length, copyProgramAt_length,
      setupDegreeChildren_length, Nat.add_assoc] using setupPC) setupActive
    setupRegs setupCB setupIndex (setupOld.trans firstOld) setupTotal setupFresh
    (setupFlag.trans firstFlag) disjoint.2 (ends.2.trans room.1.le) (by omega)
    heapBound setupWords
    (by simpa only [code, adjacencyProgramAt, List.length_append, initializeAdjacency_length,
      copyProgramAt_length, setupDegreeChildren_length, Nat.add_assoc] using codeBound)
  have lastSafe : RunFacts B H rom code (9 * (2 * t - 1) + 2) setup := by
    simpa only [code, adjacencyProgramAt, List.length_append, initializeAdjacency_length,
      copyProgramAt_length, setupDegreeChildren_length, List.append_assoc, Nat.add_assoc] using lastSafeRaw
  have firstRun : natRun rom code (22 + (9 * t + 2)) before = first := by
    rw [natRun_add rom code 22 (9 * t + 2) before, initRun]
  have both := RunFacts.add B H rom code 22 (9 * t + 2) before initSafe
    (by rw [initRun]; exact firstSafe)
  have setupWhole : natRun rom code (22 + (9 * t + 2) + 15) before = setup := by
    rw [natRun_add rom code (22 + (9 * t + 2)) 15 before, firstRun, setupRun]
  have three := RunFacts.add B H rom code (22 + (9 * t + 2)) 15 before both
    (by rw [firstRun]; exact setupSafe)
  exact RunFacts.add B H rom code (22 + (9 * t + 2) + 15) (9 * (2 * t - 1) + 2) before three
    (by rw [setupWhole]; exact lastSafe)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
