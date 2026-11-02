module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordAdjacencyRun
public import Structure.PA06_A19Prepare_StaticMetadata036_WordCards
public import Structure.PA06_A19Prepare_StaticMetadata036_WordLeafComplete
public import Structure.PA06_A19Prepare_StaticMetadata036_WordStageComplete
public import Structure.PA06_A19Prepare_StaticMetadata036_MetadataRun

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNVALIDATED same-clock composition of the unchanged532 metadata code.
The55/84 deterministic clocks and the191/202 joint witnesses are assembled
once; no independently existential Nat semantic clock is identified with a
Word safety clock. Actual finite frames establish all successor inputs and
preserve every earlier metadata result. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass OutputData actualPackedWords actualControlBase actualAllocation RunFacts)

/-- Actual complete Nat producer for all nine original metadata segments.
The only data assumptions are the shared true source caches and permanent
runtime dimensions. No lookup result, staticMetadata list, execution proof,
Word safety oracle or future-output hypothesis is an input. -/
theorem metadata_actual_joint (left right : List PackingOp) (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (before : NatState)
    (input : ScanInput q full (actualControlBase q full) (actualPackedWords q full) before)
    (children : OutputData q full (actualControlBase q full) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hpc : before.pc = 5 * left.length) (ha : before.halted = false)
    (hcodePC : Fits (indexWidth 32 full.length q)
      (5 * (left ++ metadataProgramAt left.length ++ right).length)) :
    ∃ clock ≤ metadataNatBound full.length q (preparedSize q full),
      let after := natRun (rawIncidenceROM q full) (left ++ metadataProgramAt left.length ++ right) clock before
      ScanInput q full (actualControlBase q full) (actualPackedWords q full) after ∧ CompleteMetadataWritten q full hq (actualPackedWords q full) after ∧
      (∀ position < (staticMetadata q full).length,
        after.heap (6 + actualPackedWords q full + position) = (staticMetadata q full).getD position 0) ∧
      MetadataFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧ after.register .address = actualControlBase q full ∧
      after.pc = 5 * (left.length + 532) ∧ after.halted = false ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) (left ++ metadataProgramAt left.length ++ right) clock before := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let B := metadataWordLimit bits
  let H := actualAllocation q full
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  have hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full) := rfl
  let t := preparedSize q full
  let suffix := cardsProgramAt (left.length + 55) ++ leafToolProgramAt (left.length + 139) ++
    stageProgramAt (left.length + 330) ++ right
  let code := left ++ adjacencyProgramAt left.length ++ suffix
  have codeEq : left ++ metadataProgramAt left.length ++ right = code := by
    simp only [metadataProgramAt, code, suffix, List.append_assoc]
  have codePC : Fits bits (5 * code.length) := by rw [← codeEq]; exact hcodePC
  rw [codeEq]
  let adjacent := natRun rom code (adjacencyTotalSteps t) before
  have adj := adjacency_build rom left suffix q full hq hl CB P before children input.nodes input.base hlayout hpc ha
  rcases adj with ⟨adjValues, adjFrame, adjCB, _old, _fresh, _flag, adjPC, adjActive⟩
  have adjSafe : RunFacts B H rom code (adjacencyTotalSteps t) before :=
    adjacency_actual_runFacts q full hq hl rom left suffix before children input.nodes input.base hr hpc ha
      codePC
  have adjRegs : RegistersFit bits adjacent := by
    intro reg
    exact (((adjSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
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
  have cardSafe : RunFacts B H rom code cardClock adjacent :=
    cards_actual_runFacts q full hq code (left.length + 55) cardsCode adjacent adjInput adjRegs adjPC adjActive
      codePC
  have cardRegs : RegistersFit bits cardState := by
    intro reg
    exact (((cardSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
  have leafCode : LeafToolCodeAt code (left.length + 139) := by rw [← codeEq]; exact metadata_leaf_tool_code left right
  obtain ⟨leafClock, leafBound, leafInput, leafValues, toolValues, leafFrame, leafCB, leafPC, leafActive, leafSafe⟩ :=
    leaf_tool_actual_joint q full hq code (left.length + 139) leafCode cardState cardInput cardRegs
      (by simpa only [Nat.add_assoc] using cardPC) cardActive codePC
  let leafState := natRun rom code leafClock cardState
  have leafRegs : RegistersFit bits leafState := by
    intro reg
    exact (((leafSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
  have stageCode : StageCodeAt code (left.length + 330) := by rw [← codeEq]; exact metadata_stage_code left right
  obtain ⟨stageClock, stageBound, stageInput, stageValues, stageFrame, stageCB, stagePC, stageActive, stageSafe⟩ :=
    stage_actual_joint q full hq code (left.length + 330) stageCode leafState leafInput leafRegs
      (by simpa only [Nat.add_assoc] using leafPC) leafActive codePC
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
  have firstRun : natRun rom code (adjacencyTotalSteps t + cardClock) before = cardState := by
    rw [natRun_add rom code (adjacencyTotalSteps t) cardClock before]
  have firstSafe := RunFacts.add B H rom code (adjacencyTotalSteps t) cardClock before adjSafe cardSafe
  have secondRun : natRun rom code (adjacencyTotalSteps t + cardClock + leafClock) before = leafState := by
    rw [natRun_add rom code (adjacencyTotalSteps t + cardClock) leafClock before, firstRun]
  have secondSafe := RunFacts.add B H rom code (adjacencyTotalSteps t + cardClock) leafClock before firstSafe
    (by rw [firstRun]; exact leafSafe)
  have allSafe := RunFacts.add B H rom code (adjacencyTotalSteps t + cardClock + leafClock) stageClock before secondSafe
    (by rw [secondRun]; exact stageSafe)
  refine ⟨adjacencyTotalSteps t + cardClock + leafClock + stageClock, ?_, ?_⟩
  · have adjBound := adjacencyTotalSteps_eq t ht
    dsimp only [cardClock, metadataNatBound]
    nlinarith
  · rw [actual]
    refine ⟨stageInput, complete, complete_metadata_original q full hq hl P after complete,
      metadata_frame_of_chain q full CB P before adjacent cardState leafState after adjFrame cardFrame leafFrame stageFrame,
      stageCB, ?_, stageActive, allSafe⟩
    simpa only [Nat.add_assoc] using stagePC

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
