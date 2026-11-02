module
public import Structure.PA17_A19QueryBridge_RuntimeTests_Semantics_019c
public import Structure.PA17_A19QueryBridge_RankFrame_012
public import Structure.PA17_A19QueryBridge_RankSuffix_014

/-! Genuine same-containing Tests→Ranks execution at original word32/shared F.
The test flags are produced by Tests,not supplied to the rank scan by a caller. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSemantics019
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def testsRanksClock (q size : Nat) : Nat := PA17A19RuntimeTests010.steps q size + PA17A19RuntimeRanks008.steps q

structure TestsRanksPost {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords rowBase origin : Nat) (containing : List PackingOp)
    (counts : IndexedCapacity (prepareNormalization q full).indexed)
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (node : Option (prepareNormalization q full).indexed.NodeId)
    (goodRank badRank activeValue : Nat) (before tested after : WordState bits) : Prop where
  tests : SemanticTestsPost full configuration capWords rowBase origin counts row node before tested
  tests_safe : PA17A19RuntimeTestsSafety018.TestsSafe full command capWords heapWords origin containing before
  ranks_heap : after.heap = PA17A19RuntimeRanks008.resultHeap
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)) goodRank badRank tested.heap
  active : after.halted = false
  pc : after.pc = BitVec.ofNat bits (5 * (origin + 406))
  header : after.register .address = BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
  good_rank : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 4)) = BitVec.ofNat bits goodRank
  bad_rank : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 5)) = BitVec.ofNat bits badRank
  budget : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 6)) = BitVec.ofNat bits (badRank - 1)
  mask : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 7)) =
    BitVec.ofNat bits (if activeValue = 0 then 0 else if badRank = 0 then 0 else 1)
  registers : after.register .old = BitVec.ofNat bits (if activeValue = 0 then q + 2 else goodRank) ∧
    after.register .fresh = BitVec.ofNat bits (if activeValue = 0 then 0 else badRank) ∧
    after.register .value = BitVec.ofNat bits (if activeValue = 0 then q + 2 else min goodRank (badRank + 1)) ∧
    after.register .index = BitVec.ofNat bits 0
  prefix_safe : ∀ clock < testsRanksClock q (treeSize q full),
    PA17A19RuntimeTestsSafety018.StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing clock before)
  prefix_represents : ∀ clock ≤ testsRanksClock q (treeSize q full),
    HeapRepresents q full capWords configuration (packingRun (callInput q full command) containing clock before).heap
  prefix_high : ∀ clock ≤ testsRanksClock q (treeSize q full),
    PA17A19RuntimeTests010.HighFrame (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q)
      before.heap (packingRun (callInput q full command) containing clock before).heap
  trace : (packingDynamicTrace (callInput q full command) containing (testsRanksClock q (treeSize q full)) before).length ≤
    9552 * ((q + 1) * treeSize q full)

theorem original_tests_ranks {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (factor : Nat) (h64 : 64 ≤ factor) (hmax : factor ≤ 65536)
    (hq : 0 < q) (hl : LaminarSchedule full) (containing : List PackingOp) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords factor full.length q (treeSize q full)
    let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits + factor * (full.length + q + treeSize q full + 1)
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
      (packingRun (callInput q full command) containing (testsRanksClock q (treeSize q full)) state) := by
  dsimp only
  intro emTests emRanks state rep hwidth hmask hh hp ha hi hactiveCell
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords factor full.length q (treeSize q full)
  let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits + factor * (full.length + q + treeSize q full + 1)
  let W := PSTRQueryLayout.physicalWorkspace full capWords bits
  let H := PSTRQueryLayout.header W (treeSize q full)
  let rom := callInput q full command
  let counts := IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used
  let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
  let node := PA17QueryBudget015.node full hq stage
  let good : Nat → Bool := fun b => IndexedQuery.accepts (prepareNormalization q full).indexed counts (IndexedQuery.entryAt row b)
  let bad := IndexedQuery.budgetExtensionTest (prepareNormalization q full).indexed counts row node
  let g := PA17QueryRanks011.firstFalseValue q good
  let b := PA17QueryRanks011.firstFalseValue q bad
  let T := PA17A19RuntimeTests010.steps q (treeSize q full)
  let R := PA17A19RuntimeRanks008.steps q
  let tested := packingRun rom containing T state
  let ranked := packingRun rom containing R tested
  have pair := original_tests_safe full command configuration stage factor h64 hmax hq hl containing
    emTests state rep hwidth hmask hh hp ha hi
  have sem : SemanticTestsPost full configuration capWords (PA17A19RuntimeHeader011.row full stage) origin counts row node state tested := pair.1
  have sf := pair.2
  have halloc : H + 16 + 2 * (q + 2) ≤ heapWords := PA17A19QueryBridgeNumeric006b.rank_allocated full capWords factor hq hl h64
  have hf : Fits bits heapWords := PA17A19QueryBridgeNumeric006b.heap_room full factor factor hmax hmax
  have hroom : Fits bits (H + 16 + 2 * (q + 2)) := halloc.trans_lt hf
  have hsmall : Fits bits (H + 16) := (Nat.le_add_right (H + 16) (2 * (q + 2))).trans_lt hroom
  have hgood : ∀ budget < q + 2, tested.heap (BitVec.ofNat bits (H + 16 + budget)) = BitVec.ofNat bits (bit (good budget)) := sem.good
  have hbad : ∀ budget < q + 2, tested.heap (BitVec.ofNat bits (H + 16 + budget + (q + 2))) = BitVec.ofNat bits (bit (bad budget)) := by
    intro budget hbudget
    rw [show H + 16 + budget + (q + 2) = H + 16 + (q + 2) + budget by omega]
    exact sem.bad budget hbudget
  have hinput : 1 < rom.input.length := by simp [rom, callInput, RawTreePreprocessingClaims.rawIncidenceROM]
  have hqraw : (rom.words .input).getD 1 0 = q := rfl
  have hactiveBound : PA17QueryHeader009.active full.length stage.val ≤ 1 := by
    unfold PA17QueryHeader009.active
    split_ifs <;> omega
  have hactive : (tested.heap (BitVec.ofNat bits (H + 2))).toNat = PA17QueryHeader009.active full.length stage.val := by
    rw [sem.actual.leading (H + 2) (by change H + 2 < H + 8; omega), hactiveCell, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hactiveBound.trans_lt ((show 1 ≤ H + 16 by omega).trans_lt hsmall))]
  have ranks := PA17A19RuntimeRanks008.actual_kernel emRanks rom q H good bad tested hroom hqraw hgood hbad
    sem.actual.header sem.actual.pc sem.actual.active
  rcases ranks with ⟨ractive, rpc, rheap, rold, rfresh, rvalue, rindex, raddress⟩
  have hne (left right : Nat) (hl' : left ≤ 16) (hr' : right ≤ 16) (hne' : left ≠ right) :
      BitVec.ofNat bits (H + left) ≠ BitVec.ofNat bits (H + right) := by
    intro heq
    exact hne' ((PA17A19RuntimeTests010.slots_eq_iff H left right hsmall hl' hr').mp heq)
  have tail (clock : Nat) (hc : T ≤ clock) : packingRun rom containing clock state = packingRun rom containing (clock - T) tested := by
    conv_lhs => rw [show clock = T + (clock - T) by omega]
    exact run_add rom containing T (clock - T) state
  have hrun : packingRun rom containing (testsRanksClock q (treeSize q full)) state = ranked := by
    unfold testsRanksClock
    rw [run_add]
  rw [hrun]
  refine ⟨sem, sf, rheap, ractive, ?_, raddress, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using rpc
  · rw [rheap, PA17A19RuntimeRanks008.resultHeap,
      Function.update_of_ne (hne 4 7 (by decide) (by decide) (by decide)),
      Function.update_of_ne (hne 4 6 (by decide) (by decide) (by decide)),
      Function.update_of_ne (hne 4 5 (by decide) (by decide) (by decide)), Function.update_self]
  · rw [rheap, PA17A19RuntimeRanks008.resultHeap,
      Function.update_of_ne (hne 5 7 (by decide) (by decide) (by decide)),
      Function.update_of_ne (hne 5 6 (by decide) (by decide) (by decide)), Function.update_self]
  · rw [rheap, PA17A19RuntimeRanks008.resultHeap,
      Function.update_of_ne (hne 6 7 (by decide) (by decide) (by decide)), Function.update_self]
  · rw [rheap, PA17A19RuntimeRanks008.resultHeap, Function.update_self, hactive]
  · change ranked.register .old = BitVec.ofNat bits
        (if (tested.heap (BitVec.ofNat bits (H + 2))).toNat = 0 then q + 2 else g) at rold
    change ranked.register .fresh = BitVec.ofNat bits
        (if (tested.heap (BitVec.ofNat bits (H + 2))).toNat = 0 then 0 else b) at rfresh
    change ranked.register .value = BitVec.ofNat bits
        (if (tested.heap (BitVec.ofNat bits (H + 2))).toNat = 0 then q + 2 else min g (b + 1)) at rvalue
    rw [hactive] at rold rfresh rvalue
    exact ⟨rold, rfresh, rvalue, rindex⟩
  · intro clock hc
    by_cases ht : clock < T
    · exact sf.prefix_safe clock ht
    · rw [tail clock (by omega)]
      exact PA17A19RuntimeRanks008.actual_prefix_decoded emRanks rom q H heapWords good bad tested hroom halloc hinput hqraw
        hgood hbad sem.actual.header sem.actual.pc sem.actual.active (clock - T) (by change clock < T + R at hc; omega)
  · intro clock hc
    by_cases ht : clock ≤ T
    · have bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords := by
        simp only [capWords, capacityWords, ne_of_gt hq, ite_false]; omega
      exact PA17A19RuntimeTests010.represents_of_leading_frame full configuration capWords state.heap _
        (by have hb := PA17A19QueryBridgeNumeric006b.bits_eight full.length q; omega) hq rep bitmap
        (PA17A19QueryBridgeNumeric006b.scalar_room full factor hmax) hsmall (sf.leading clock ht)
    · rw [tail clock (by omega)]
      exact PA17A19QueryBridgeRankFrame012.original_rank_prefix_represents full command configuration factor factor
        hmax hmax h64 hq hl containing emRanks tested sem.represents good bad hgood hbad
        sem.actual.header sem.actual.pc sem.actual.active (clock - T) (by change clock ≤ T + R at hc; omega)
  · intro clock hc
    by_cases ht : clock ≤ T
    · exact sf.high clock ht
    · rw [tail clock (by omega)]
      apply (sf.high T (by omega)).trans
      intro physical hphysical hge
      exact PA17A19RankSuffix014.actual_endpoint_frame emRanks rom W (treeSize q full) q heapWords good bad tested
        hroom halloc hinput hqraw hgood hbad sem.actual.header sem.actual.pc sem.actual.active
        (clock - T) (by change clock ≤ T + R at hc; omega) physical hphysical hge
  · have ht : 0 < treeSize q full := by
      let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
      obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
      have hpositive : 0 < (prepareNormalization q full).indexed.nodes.size :=
        Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
      simpa only [treeSize, ne_of_gt hq, ite_false] using hpositive
    have htrace := packingDynamicTrace_length_le rom containing (testsRanksClock q (treeSize q full)) state
    have hT := PA17A19RuntimeTests010.steps_bound q (treeSize q full) ht
    have hR : PA17A19RuntimeRanks008.steps q ≤ 68 * (q + 1) := by unfold PA17A19RuntimeRanks008.steps; omega
    have hwork : q + 1 ≤ (q + 1) * treeSize q full := Nat.le_mul_of_pos_right _ ht
    change (packingDynamicTrace rom containing (testsRanksClock q (treeSize q full)) state).length ≤
      9552 * ((q + 1) * treeSize q full)
    unfold testsRanksClock at htrace ⊢
    omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSemantics019
