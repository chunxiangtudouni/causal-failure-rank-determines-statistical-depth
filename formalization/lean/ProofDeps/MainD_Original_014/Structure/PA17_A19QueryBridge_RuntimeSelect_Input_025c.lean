module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_Input_025b

/-! Original word32/shared8192 actual selector: ParentInputs, numeric layout
and physical source vectors are constructed from the current same-call
original Inputs and the actual saved firstFalse budget. No free safe-run,
candidate/tool, physical-card, height or initialized-scratch qualification. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelectInput025

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeSelect009

theorem actual_original_selector {q origin : Nat} (full : List (Finset (Fin q)))
    (command : Command) (configuration : Configuration q) (stage : Fin (full.length + 1))
    (hq : 0 < q) (hl : LaminarSchedule full) (containing : List PackingOp) :
    let bits := indexWidth 32 full.length q
    let C := capacityWords 8192 full.length q (treeSize q full)
    let words := physicalHeaderWords + packedCapacityWords q C bits + 8192 * (full.length + q + treeSize q full + 1)
    let W := PSTRQueryLayout.physicalWorkspace full C bits
    let H := PSTRQueryLayout.header W (treeSize q full)
    let L := PSTRQueryLayout.logicalWorkspace full C
    let counts := IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used
    let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
    let node := PA17QueryBudget015.node full hq stage
    let b := PA17QueryRanks011.firstFalseValue q
      (IndexedQuery.budgetExtensionTest (prepareNormalization q full).indexed counts row node)
    let rowBase := PA17A19RuntimeHeader011.row full stage
    ∀ (_ : CoreEmbedded bits origin containing) (state : WordState bits),
    HeapRepresents q full C configuration state.heap →
    state.heap (BitVec.ofNat bits (W + 12)) = BitVec.ofNat bits (CapacityBits.width q) →
    state.heap (BitVec.ofNat bits (W + 13)) = lowMask bits (CapacityBits.width q) →
    state.register .address = BitVec.ofNat bits H → state.pc = BitVec.ofNat bits (5 * origin) → state.halted = false →
    PA17QueryTests009.Inputs (prepareNormalization q full).indexed
      (PSTRQueryLayout.header L (treeSize q full)) (PSTRQueryLayout.countsBase L)
      (PSTRQueryLayout.parentsBase L (treeSize q full)) (PSTRQueryLayout.header L (treeSize q full) + 1)
      rowBase counts row node (logicalHeap q C state.heap) →
    state.heap (BitVec.ofNat bits (H + 6)) = BitVec.ofNat bits (b - 1) →
    let after := packingRun (callInput q full command) containing (coreSteps (treeSize q full)) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 281)) ∧
      after.register .address = BitVec.ofNat bits H ∧
      after.heap (BitVec.ofNat bits (toolSlot H q (treeSize q full))) =
        BitVec.ofNat bits (PA17LeafLabels005.encodeTool
          (node.bind (IndexedDescent.selectAt (prepareNormalization q full).indexed
            (IndexedDescent.leafTools (prepareNormalization q full).indexed) counts
            (actualPayloadCapacity full C rowBase (b - 1) state.heap)))) ∧
      (∀ clock < coreSteps (treeSize q full), DecodedAt (callInput q full command) containing words
        (packingRun (callInput q full command) containing clock state)) ∧
      (∀ clock ≤ coreSteps (treeSize q full), ∀ physical, Fits bits physical →
        (physical < H + 8 ∨ PA17A19RuntimeSelect009.endpoint H q (treeSize q full) ≤ physical) →
        (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) =
          state.heap (BitVec.ofNat bits physical)) ∧
      (∀ clock ≤ coreSteps (treeSize q full), HeapRepresents q full C configuration
        (packingRun (callInput q full command) containing clock state).heap) ∧
      (packingDynamicTrace (callInput q full command) containing (coreSteps (treeSize q full)) state).length ≤
        3600 * (treeSize q full + 1) := by
  dsimp only
  intro em state rep hwidth hmask hh hp ha hi hselected
  let bits := indexWidth 32 full.length q
  let C := capacityWords 8192 full.length q (treeSize q full)
  let counts := IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used
  let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
  let node := PA17QueryBudget015.node full hq stage
  let rowBase := PA17A19RuntimeHeader011.row full stage
  let test := IndexedQuery.budgetExtensionTest (prepareNormalization q full).indexed counts row node
  let b := PA17QueryRanks011.firstFalseValue q test
  have hb : b - 1 ≤ q + 1 := by
    have hh := PA17QueryRanks011.firstFalseValue_le q test
    omega
  have layout := original_layout full stage (b - 1) hq hl hb
  have data := parentInputs_of_inputs full configuration C rowBase (b - 1) counts row node state hq
    rep hwidth hmask hi hb hselected hh hp ha
  have sources := sources_of_inputs full C rowBase (b - 1) counts row node state.heap hq hi
  have slots := PA17A19RuntimeTestsSemantics019.inputs_word_slots full C rowBase counts row node state hq hi
  exact actual_selector em layout command configuration state data counts
    (actualPayloadCapacity full C rowBase (b - 1) state.heap) sources node slots.2.1

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelectInput025
