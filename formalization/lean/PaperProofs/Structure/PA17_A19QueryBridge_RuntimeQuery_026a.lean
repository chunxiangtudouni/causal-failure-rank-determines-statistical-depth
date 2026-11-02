module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Semantics_019e

/-! The same actual Tests→Ranks run preserves every physical word below H+4.
The original logical Inputs therefore survive at the actual rank exit; the
logical protection limit is H+4, including when physical H is below capacity. -/

@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeQuery026

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem tests_ranks_prefix_leading_of_post {bits q origin : Nat}
    (full : List (Finset (Fin q))) (command : Command) (configuration : Configuration q)
    (capWords heapWords rowBase : Nat) (containing : List PackingOp)
    (counts : IndexedCapacity (prepareNormalization q full).indexed)
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (node : Option (prepareNormalization q full).indexed.NodeId)
    (goodRank badRank activeValue : Nat) (state : WordState bits)
    (emRanks : PA17A19RuntimeRanks008.Embedded bits (origin + 355) containing)
    (post : PA17A19RuntimeTestsSemantics019.TestsRanksPost full command configuration capWords heapWords
      rowBase origin containing counts row node goodRank badRank activeValue state
      (packingRun (callInput q full command) containing (PA17A19RuntimeTests010.steps q (treeSize q full)) state)
      (packingRun (callInput q full command) containing
        (PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full)) state))
    (hroom : Fits bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16 + 2 * (q + 2)))
    (halloc : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16 + 2 * (q + 2) ≤ heapWords) :
    ∀ clock ≤ PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full),
      ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
        (treeSize q full) + 4,
      (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) =
        state.heap (BitVec.ofNat bits physical) := by
  let rom := callInput q full command
  let H := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
  let T := PA17A19RuntimeTests010.steps q (treeSize q full)
  let tested := packingRun rom containing T state
  let good : Nat → Bool := fun budget =>
    IndexedQuery.accepts (prepareNormalization q full).indexed counts (IndexedQuery.entryAt row budget)
  let bad := IndexedQuery.budgetExtensionTest (prepareNormalization q full).indexed counts row node
  have hgood : ∀ budget < q + 2,
      tested.heap (BitVec.ofNat bits (H + 16 + budget)) = BitVec.ofNat bits (bit (good budget)) :=
    post.tests.good
  have hbad : ∀ budget < q + 2,
      tested.heap (BitVec.ofNat bits (H + 16 + budget + (q + 2))) =
        BitVec.ofNat bits (bit (bad budget)) := by
    intro budget hbudget
    rw [show H + 16 + budget + (q + 2) = H + 16 + (q + 2) + budget by omega]
    exact post.tests.bad budget hbudget
  have hinput : 1 < rom.input.length := by
    simp [rom, callInput, RawTreePreprocessingClaims.rawIncidenceROM]
  have hqraw : (rom.words .input).getD 1 0 = q := rfl
  intro clock hc physical hphysical
  by_cases ht : clock ≤ T
  · exact post.tests_safe.leading clock ht physical (by change physical < H + 8; omega)
  · have tail : packingRun rom containing clock state = packingRun rom containing (clock - T) tested := by
      conv_lhs => rw [show clock = T + (clock - T) by omega]
      exact run_add rom containing T (clock - T) state
    change (packingRun rom containing clock state).heap _ = _
    rw [tail]
    have hrank := PA17A19RuntimeRanks008.actual_leading_frame emRanks rom q H heapWords good bad tested
      hroom halloc hinput hqraw hgood hbad post.tests.actual.header post.tests.actual.pc
      post.tests.actual.active (clock - T)
      (by change clock ≤ T + PA17A19RuntimeRanks008.steps q at hc; omega) physical hphysical
    exact hrank.trans (post.tests_safe.leading T (by omega) physical (by change physical < H + 8; omega))

theorem logical_leading_four_frame {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords size : Nat) (old fresh : BitVec bits → BitVec bits)
    (hb : 0 < bits) (hq : 0 < q)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) size + 16))
    (hframe : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) size + 4,
      fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical))
    (logical : Nat)
    (hl : logical < PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) size + 4) :
    logicalHeap q capWords fresh logical = logicalHeap q capWords old logical := by
  let physicalHeader := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) size
  let indexWords := 2 + (staticMetadata q full).length + 16 + size + size + 1 + 4
  refine PSTRRepairHeap.logical_frame old fresh capWords indexWords (physicalHeader + 4) logical hb hq hs
    ((show physicalHeader + 4 + 3 ≤ physicalHeader + 16 by omega).trans_lt hroom) ?_ hframe ?_
  · unfold physicalHeader indexWords PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      PSTRQueryLayout.physicalWorkspace PSTRStaticHeap.metadataAddress physicalHeaderWords
    omega
  · unfold indexWords PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      PSTRQueryLayout.logicalWorkspace at *
    omega

theorem original_tests_ranks_inputs_8192 {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (hq : 0 < q) (hl : LaminarSchedule full) (containing : List PackingOp) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords 8192 full.length q (treeSize q full)
    let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits +
      8192 * (full.length + q + treeSize q full + 1)
    let W := PSTRQueryLayout.physicalWorkspace full capWords bits
    let H := PSTRQueryLayout.header W (treeSize q full)
    let L := PSTRQueryLayout.logicalWorkspace full capWords
    let counts := IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used
    let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
    let node := PA17QueryBudget015.node full hq stage
    let g := PA17QueryRanks011.firstFalseValue q
      (fun budget => IndexedQuery.accepts (prepareNormalization q full).indexed counts (IndexedQuery.entryAt row budget))
    let b := PA17QueryRanks011.firstFalseValue q
      (IndexedQuery.budgetExtensionTest (prepareNormalization q full).indexed counts row node)
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
    PA17A19RuntimeTestsSemantics019.TestsRanksPost full command configuration capWords heapWords
      (PA17A19RuntimeHeader011.row full stage) origin containing counts row node g b
      (PA17QueryHeader009.active full.length stage.val) state
      (packingRun (callInput q full command) containing (PA17A19RuntimeTests010.steps q (treeSize q full)) state)
      (packingRun (callInput q full command) containing
        (PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full)) state) ∧
    (∀ clock ≤ PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full), ∀ physical < H + 4,
      (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) =
        state.heap (BitVec.ofNat bits physical)) ∧
    PA17QueryTests009.Inputs (prepareNormalization q full).indexed (PSTRQueryLayout.header L (treeSize q full))
      (PSTRQueryLayout.countsBase L) (PSTRQueryLayout.parentsBase L (treeSize q full))
      (PSTRQueryLayout.header L (treeSize q full) + 1) (PA17A19RuntimeHeader011.row full stage)
      counts row node (logicalHeap q capWords (packingRun (callInput q full command) containing
        (PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full)) state).heap) := by
  dsimp only
  intro emTests emRanks state rep hwidth hmask hh hp ha hi hactiveCell
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits +
    8192 * (full.length + q + treeSize q full + 1)
  let H := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
  have post := PA17A19RuntimeTestsSemantics019.original_tests_ranks_8192 full command configuration stage hq hl
    containing emTests emRanks state rep hwidth hmask hh hp ha hi hactiveCell
  have halloc : H + 16 + 2 * (q + 2) ≤ heapWords :=
    PA17A19QueryBridgeNumeric006b.rank_allocated full capWords 8192 hq hl (by decide)
  have hf : Fits bits heapWords :=
    PA17A19QueryBridgeNumeric006b.heap_room full 8192 8192 (by decide) (by decide)
  have hroom : Fits bits (H + 16 + 2 * (q + 2)) := halloc.trans_lt hf
  have hsmall : Fits bits (H + 16) := (Nat.le_add_right (H + 16) (2 * (q + 2))).trans_lt hroom
  have leading := tests_ranks_prefix_leading_of_post full command configuration capWords heapWords
    (PA17A19RuntimeHeader011.row full stage) containing _ _ _ _ _ _ state emRanks post hroom halloc
  refine ⟨post, leading, ?_⟩
  have htable : tableWords full.length q (treeSize q full) ≤ capWords := by
    simp only [capWords, capacityWords, ne_of_gt hq, ite_false]
    omega
  have hread := PA17A19RuntimeHeader011.read_bounds full capWords stage htable
  have hsize : treeSize q full = (prepareNormalization q full).indexed.nodes.size := by
    simp only [treeSize, ne_of_gt hq, ite_false]
  apply hi.transfer (protectedLimit := PA17A19RuntimeHeader011.logicalHead full capWords + 4)
  · simpa only [← hsize, PA17A19RuntimeHeader011.logicalHead, capWords] using hread
  · intro logical hlogical
    exact logical_leading_four_frame full capWords (treeSize q full) state.heap _
      (by have hb := PA17A19QueryBridgeNumeric006b.bits_eight full.length q; omega) hq
      (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) hsmall
      (leading _ (by omega)) logical hlogical

theorem original_tests_ranks_prefix_leading_8192 {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (hq : 0 < q) (hl : LaminarSchedule full) (containing : List PackingOp) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords 8192 full.length q (treeSize q full)
    let W := PSTRQueryLayout.physicalWorkspace full capWords bits
    let H := PSTRQueryLayout.header W (treeSize q full)
    let L := PSTRQueryLayout.logicalWorkspace full capWords
    let counts := IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used
    let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
    let node := PA17QueryBudget015.node full hq stage
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
    ∀ clock ≤ PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full), ∀ physical < H + 4,
      (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) =
        state.heap (BitVec.ofNat bits physical) := by
  dsimp only
  intro emTests emRanks state rep hwidth hmask hh hp ha hi hactiveCell
  exact (original_tests_ranks_inputs_8192 full command configuration stage hq hl containing emTests emRanks state
    rep hwidth hmask hh hp ha hi hactiveCell).2.1

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeQuery026
