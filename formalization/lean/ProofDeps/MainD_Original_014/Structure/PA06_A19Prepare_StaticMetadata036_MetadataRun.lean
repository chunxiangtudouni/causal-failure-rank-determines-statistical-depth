module

public import Structure.PA06_A19Prepare_StaticMetadata036_MetadataFrames

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Single fixed532-op complete Nat staticMetadata producer: true adjacency
copies, all card/internal entries, full leaf/tool scan, full stage scan.
It must be placed after actual DP/fullBuild and before037/033. All ordinary
output values are derived from the same actual raw/023 caches. This package
still requires strict validation and the full-prefix Word refinement. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass OutputData)

def metadataProgramAt (start : Nat) : List PackingOp :=
  adjacencyProgramAt start ++ cardsProgramAt (start + 55) ++
    leafToolProgramAt (start + 139) ++ stageProgramAt (start + 330)

theorem metadataProgramAt_length (start : Nat) : (metadataProgramAt start).length = 532 := rfl

theorem metadata_cards_code (left right : List PackingOp) :
    CardsCodeAt (left ++ metadataProgramAt left.length ++ right) (left.length + 55) := by
  have h := cards_append_code (left ++ adjacencyProgramAt left.length)
    (leafToolProgramAt (left.length + 139) ++ stageProgramAt (left.length + 330) ++ right)
  simpa only [metadataProgramAt, List.length_append, adjacencyProgramAt_length,
    List.append_assoc] using h

theorem metadata_leaf_tool_code (left right : List PackingOp) :
    LeafToolCodeAt (left ++ metadataProgramAt left.length ++ right) (left.length + 139) := by
  have h := leafTool_append_code (left ++ adjacencyProgramAt left.length ++ cardsProgramAt (left.length + 55))
    (stageProgramAt (left.length + 330) ++ right)
  simpa only [metadataProgramAt, List.length_append, adjacencyProgramAt_length,
    cardsProgramAt_length, List.append_assoc, Nat.add_assoc] using h

theorem metadata_stage_code (left right : List PackingOp) :
    StageCodeAt (left ++ metadataProgramAt left.length ++ right) (left.length + 330) := by
  have h := stage_append_code (left ++ adjacencyProgramAt left.length ++ cardsProgramAt (left.length + 55) ++
    leafToolProgramAt (left.length + 139)) right
  simpa only [metadataProgramAt, List.length_append, adjacencyProgramAt_length,
    cardsProgramAt_length, leafToolProgramAt_length, List.append_assoc, Nat.add_assoc] using h

def metadataNatBound (N q t : Nat) : Nat :=
  71 + t * (174 + 116 * q) + N * (50 + t * (63 + 90 * q))

/-- Actual complete Nat producer for all nine original metadata segments.
The only data assumptions are the shared true source caches and permanent
runtime dimensions. No lookup result, staticMetadata list, execution proof,
Word safety oracle or future-output hypothesis is an input. -/
theorem metadata_build (left right : List PackingOp) (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (CB P : Nat) (before : NatState)
    (input : ScanInput q full CB P before) (children : OutputData q full CB before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hpc : before.pc = 5 * left.length) (ha : before.halted = false) :
    ∃ clock ≤ metadataNatBound full.length q (preparedSize q full),
      let after := natRun (rawIncidenceROM q full) (left ++ metadataProgramAt left.length ++ right) clock before
      ScanInput q full CB P after ∧ CompleteMetadataWritten q full hq P after ∧
      (∀ position < (staticMetadata q full).length,
        after.heap (6 + P + position) = (staticMetadata q full).getD position 0) ∧
      MetadataFrame q full CB P before after ∧ after.register .address = CB ∧
      after.pc = 5 * (left.length + 532) ∧ after.halted = false := by
  let rom := rawIncidenceROM q full
  let t := preparedSize q full
  let suffix := cardsProgramAt (left.length + 55) ++ leafToolProgramAt (left.length + 139) ++
    stageProgramAt (left.length + 330) ++ right
  let code := left ++ adjacencyProgramAt left.length ++ suffix
  have codeEq : left ++ metadataProgramAt left.length ++ right = code := by
    simp only [metadataProgramAt, code, suffix, List.append_assoc]
  rw [codeEq]
  let adjacent := natRun rom code (adjacencyTotalSteps t) before
  have adj := adjacency_build rom left suffix q full hq hl CB P before children input.nodes input.base hlayout hpc ha
  rcases adj with ⟨adjValues, adjFrame, adjCB, _old, _fresh, _flag, adjPC, adjActive⟩
  have ht : 0 < t := by
    have h := PA06A19PrepareControlBank017.treeSize_pos full hq
    simpa only [treeSize, Nat.ne_of_gt hq, ite_false] using h
  have adjEnd : 6 + P + 3 * t ≤ CB := by
    rw [hlayout]
    exact adjacency_below_control (mass q full) t P ht
  have adjInput : ScanInput q full CB P adjacent := ScanInput.of_high_eq input
    (fun address ha => adjFrame address (Or.inr (by omega))) adjCB
  have cardsCode : CardsCodeAt code (left.length + 55) := by rw [← codeEq]; exact metadata_cards_code left right
  let cardClock := 13 + 80 * t
  let cardState := natRun rom code cardClock adjacent
  have cards := cards_build q full CB P code (left.length + 55) cardsCode adjacent adjInput hlayout adjPC adjActive
  rcases cards with ⟨cardInput, cardValues, cardFrame, cardCB, cardPC, cardActive⟩
  have leafCode : LeafToolCodeAt code (left.length + 139) := by rw [← codeEq]; exact metadata_leaf_tool_code left right
  obtain ⟨leafClock, leafBound, leafInput, leafValues, toolValues, leafFrame, leafCB, leafPC, leafActive⟩ :=
    leaf_tool_build q full hq CB P code (left.length + 139) leafCode cardState cardInput hlayout
      (by simpa only [Nat.add_assoc] using cardPC) cardActive
  let leafState := natRun rom code leafClock cardState
  have stageCode : StageCodeAt code (left.length + 330) := by rw [← codeEq]; exact metadata_stage_code left right
  obtain ⟨stageClock, stageBound, stageInput, stageValues, stageFrame, stageCB, stagePC, stageActive⟩ :=
    stage_build q full hq CB P code (left.length + 330) stageCode leafState leafInput hlayout
      (by simpa only [Nat.add_assoc] using leafPC) leafActive
  let after := natRun rom code stageClock leafState
  have adjFinal := adjacency_preserved q full hq hl CB P adjacent cardState leafState after
    adjValues cardFrame leafFrame stageFrame hlayout
  have scalarFinal := scalars_preserved q full CB P cardState leafState after cardValues leafFrame stageFrame hlayout
  have lookupFrame := lookup_preserved q full CB P leafState after stageFrame hlayout
  have complete : CompleteMetadataWritten q full hq P after := by
    refine ⟨adjFinal, fun node => (scalarFinal node).1, fun node => (scalarFinal node).2, ?_, stageValues, ?_⟩
    · intro node
      rw [lookupFrame.1 node]
      exact leafValues node
    · intro tool
      rw [lookupFrame.2 tool]
      exact toolValues tool
  have actual : natRun rom code (adjacencyTotalSteps t + cardClock + leafClock + stageClock) before = after := by
    rw [natRun_add, natRun_add, natRun_add]
  refine ⟨adjacencyTotalSteps t + cardClock + leafClock + stageClock, ?_, ?_⟩
  · have adjBound := adjacencyTotalSteps_eq t ht
    dsimp only [cardClock, metadataNatBound]
    nlinarith
  · rw [actual]
    refine ⟨stageInput, complete, complete_metadata_original q full hq hl P after complete,
      metadata_frame_of_chain q full CB P before adjacent cardState leafState after adjFrame cardFrame leafFrame stageFrame,
      stageCB, ?_, stageActive⟩
    simpa only [Nat.add_assoc] using stagePC

/-- Constant-factor original treeWork bound for the entire true Nat
metadata run. This is not a claim that Word refinement has been closed. -/
theorem metadata_steps_treeWork (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (clock : Nat)
    (hc : clock ≤ metadataNatBound full.length q (preparedSize q full)) : clock ≤ 1000 * treeWork full.length q := by
  let N := full.length
  let t := preparedSize q full
  let M := N + q + 1
  have ht : t ≤ M := prepared_indexed_size_le q full
  have hN : N ≤ M := by dsimp only [M]; omega
  have hM : M ≤ M ^ 2 := by dsimp only [M]; nlinarith
  have hMq : M ^ 2 ≤ M ^ 2 * q := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (M ^ 2) (show 1 ≤ q by omega)
  have htq : t * q ≤ M ^ 2 * q := Nat.mul_le_mul_right q (ht.trans hM)
  have ht' : t ≤ M ^ 2 * q := (ht.trans hM).trans hMq
  have hN' : N ≤ M ^ 2 * q := (hN.trans hM).trans hMq
  have hNt : N * t ≤ M ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hN ht
  have hNtq := Nat.mul_le_mul_right q hNt
  have hNt' : N * t ≤ M ^ 2 * q := hNt.trans hMq
  have hpos : 0 < M ^ 2 * q := Nat.mul_pos (pow_pos (by dsimp only [M]; omega) 2) hq
  change clock ≤ 1000 * (M ^ 2 * q)
  change clock ≤ 71 + t * (174 + 116 * q) + N * (50 + t * (63 + 90 * q)) at hc
  nlinarith

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
