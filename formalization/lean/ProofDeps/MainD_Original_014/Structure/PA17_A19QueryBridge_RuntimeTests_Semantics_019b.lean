module
public import Structure.PA17_A19QueryBridge_RuntimeTests_Semantics_019a
public import Structure.PA17_A19QueryBridge_Numeric_006b

/-! Original word32 and one shared implementation factor discharge every
numeric/bitmap/row/parent qualification of the actual semantic Tests run. -/
@[expose] public section
set_option maxRecDepth 28000
set_option maxHeartbeats 2800000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSemantics019
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem original_tests_semantic {q origin : Nat} (full : List (Finset (Fin q)))
    (command : Command) (configuration : Configuration q) (stage : Fin (full.length + 1))
    (factor : Nat) (h64 : 64 ≤ factor) (hmax : factor ≤ 65536)
    (hq : 0 < q) (hl : LaminarSchedule full) (containing : List PackingOp) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords factor full.length q (treeSize q full)
    let W := PSTRQueryLayout.physicalWorkspace full capWords bits
    let H := PSTRQueryLayout.header W (treeSize q full)
    let L := PSTRQueryLayout.logicalWorkspace full capWords
    let counts := IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used
    let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
    let node := PA17QueryBudget015.node full hq stage
    ∀ (_ : PA17A19RuntimeTests010.Embedded bits origin containing) (state : WordState bits),
    HeapRepresents q full capWords configuration state.heap →
    state.heap (BitVec.ofNat bits (W + 12)) = BitVec.ofNat bits (CapacityBits.width q) →
    state.heap (BitVec.ofNat bits (W + 13)) = lowMask bits (CapacityBits.width q) →
    state.register .address = BitVec.ofNat bits H →
    state.pc = BitVec.ofNat bits (5 * origin) → state.halted = false →
    PA17QueryTests009.Inputs (prepareNormalization q full).indexed
      (PSTRQueryLayout.header L (treeSize q full)) (PSTRQueryLayout.countsBase L)
      (PSTRQueryLayout.parentsBase L (treeSize q full)) (PSTRQueryLayout.header L (treeSize q full) + 1)
      (PA17A19RuntimeHeader011.row full stage) counts row node (logicalHeap q capWords state.heap) →
    SemanticTestsPost full configuration capWords (PA17A19RuntimeHeader011.row full stage)
      origin counts row node state
      (packingRun (callInput q full command) containing (PA17A19RuntimeTests010.steps q (treeSize q full)) state) := by
  dsimp only
  intro em state rep hwidth hmask hh hp ha hi
  let capWords := capacityWords factor full.length q (treeSize q full)
  let bits := indexWidth 32 full.length q
  let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits +
    factor * (full.length + q + treeSize q full + 1)
  have bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords := by
    simp only [capWords, capacityWords, ne_of_gt hq, ite_false]
    omega
  have hrow := PA17QueryBudget015.row_fits_table full.length q (treeSize q full)
    (PA17QueryBudget015.rowIndex full stage)
  have htable : tableWords full.length q (treeSize q full) ≤ capWords := by omega
  apply actual_tests_semantic em full command configuration capWords heapWords
    (PA17A19RuntimeHeader011.row full stage)
    (IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used)
    (IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage))
    (PA17QueryBudget015.node full hq stage) state
    (PA17A19QueryBridgeNumeric006b.bits_eight full.length q) hq
    (PA17PackingBounds043.width_le_bits full.length q) rep bitmap
    (PA17A19QueryBridgeNumeric006b.scalar_room full factor hmax)
    (PA17A19QueryBridgeNumeric006b.heap_room full factor factor hmax hmax)
    (PSTRQueryLayout.endpoint_index_factor full capWords bits factor hq hl h64)
    hwidth hmask hh hp ha hi
  exact hrow.trans htable

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSemantics019
