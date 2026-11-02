module
public import Structure.PA17_A19QueryBridge_RuntimeTests_Semantics_019d
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSemantics019
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem original_tests_ranks_8192 {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (hq : 0 < q) (hl : LaminarSchedule full) (containing : List PackingOp) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords 8192 full.length q (treeSize q full)
    let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits + 8192 * (full.length + q + treeSize q full + 1)
    let W := PSTRQueryLayout.physicalWorkspace full capWords bits
    let H := PSTRQueryLayout.header W (treeSize q full)
    let L := PSTRQueryLayout.logicalWorkspace full capWords
    let counts := IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used
    let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
    let node := PA17QueryBudget015.node full hq stage
    let g := PA17QueryRanks011.firstFalseValue q (fun b => IndexedQuery.accepts (prepareNormalization q full).indexed counts (IndexedQuery.entryAt row b))
    let b := PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest (prepareNormalization q full).indexed counts row node)
    ∀ (_ : PA17A19RuntimeTests010.Embedded bits origin containing)
      (_ : PA17A19RuntimeRanks008.Embedded bits (origin + 355) containing) (state : WordState bits),
    HeapRepresents q full capWords configuration state.heap →
    state.heap (BitVec.ofNat bits (W + 12)) = BitVec.ofNat bits (CapacityBits.width q) →
    state.heap (BitVec.ofNat bits (W + 13)) = lowMask bits (CapacityBits.width q) →
    state.register .address = BitVec.ofNat bits H → state.pc = BitVec.ofNat bits (5 * origin) → state.halted = false →
    PA17QueryTests009.Inputs (prepareNormalization q full).indexed (PSTRQueryLayout.header L (treeSize q full))
      (PSTRQueryLayout.countsBase L) (PSTRQueryLayout.parentsBase L (treeSize q full))
      (PSTRQueryLayout.header L (treeSize q full) + 1) (PA17A19RuntimeHeader011.row full stage)
      counts row node (logicalHeap q capWords state.heap) →
    state.heap (BitVec.ofNat bits (H + 2)) = BitVec.ofNat bits (PA17QueryHeader009.active full.length stage.val) →
    TestsRanksPost full command configuration capWords heapWords (PA17A19RuntimeHeader011.row full stage) origin containing counts row node
      g b (PA17QueryHeader009.active full.length stage.val) state
      (packingRun (callInput q full command) containing (PA17A19RuntimeTests010.steps q (treeSize q full)) state)
      (packingRun (callInput q full command) containing (testsRanksClock q (treeSize q full)) state) :=
  original_tests_ranks full command configuration stage 8192 (by decide) (by decide) hq hl containing

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSemantics019
