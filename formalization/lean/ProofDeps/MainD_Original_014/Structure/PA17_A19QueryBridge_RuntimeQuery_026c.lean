module

public import Structure.PA17_A19QueryBridge_RuntimeQuery_026b

/-! Every clock of the one real719-op query tail inherits actual fetch,
decode,access and persistent frames from its executed phase. Raw packed
table words,including VOID payload,are preserved by a genuine logical frame. -/

@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeQuery026

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem tailClock_bound (q size : Nat) (ht : 0 < size) : tailClock q size ≤ 1128 * ((q + 1) * size) := by
  let work := (q + 1) * size
  have hw : q + 1 ≤ work := Nat.le_mul_of_pos_right _ ht
  have hs : size ≤ work := Nat.le_mul_of_pos_left _ (by omega)
  have hT := PA17A19RuntimeTests010.steps_bound q size ht
  have hR : PA17A19RuntimeRanks008.steps q ≤ 68 * work := by
    have hr : PA17A19RuntimeRanks008.steps q ≤ 68 * (q + 1) := by
      unfold PA17A19RuntimeRanks008.steps
      omega
    exact hr.trans (Nat.mul_le_mul_left 68 hw)
  have hS : PA17A19RuntimeSelect009.coreSteps size ≤ 300 * work := by
    have hh : PA17A19RuntimeSelect009.coreSteps size ≤ 300 * size := by
      rw [PA17A19RuntimeSelect009.coreSteps_eq]
      omega
    exact hh.trans (Nat.mul_le_mul_left 300 hs)
  change PA17A19RuntimeTests010.steps q size ≤ 728 * work at hT
  change tailClock q size ≤ 1128 * work
  unfold tailClock PA17A19RuntimeTestsSemantics019.testsRanksClock
  omega

structure TailComplete {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (capWords heapWords origin : Nat) (containing : List PackingOp) (before after : WordState bits) : Prop where
  data : TailData full command configuration stage hq capWords heapWords origin containing before after
  correct : ReplyCorrect q (callback q full stage configuration.used) (replyState q capWords after)
  active : after.halted = false
  pc : after.pc = BitVec.ofNat bits (5 * (origin + 719))
  header : after.register .address = BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
  prefix_safe : ∀ clock < tailClock q (treeSize q full),
    PA17A19RuntimeTestsSafety018.StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing clock before)
  prefix_represents : ∀ clock ≤ tailClock q (treeSize q full),
    HeapRepresents q full capWords configuration (packingRun (callInput q full command) containing clock before).heap
  prefix_low : ∀ clock ≤ tailClock q (treeSize q full), ∀ physical,
    physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 4 →
      (packingRun (callInput q full command) containing clock before).heap (BitVec.ofNat bits physical) =
        before.heap (BitVec.ofNat bits physical)
  prefix_high : ∀ clock ≤ tailClock q (treeSize q full),
    PA17A19RuntimeTests010.HighFrame
      (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q)
      before.heap (packingRun (callInput q full command) containing clock before).heap
  prefix_logical : ∀ clock ≤ tailClock q (treeSize q full), ∀ address,
    address < PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + 4 →
      logicalHeap q capWords (packingRun (callInput q full command) containing clock before).heap address =
        logicalHeap q capWords before.heap address
  prefix_capacity : ∀ clock ≤ tailClock q (treeSize q full), ∀ address < capWords,
    logicalHeap q capWords (packingRun (callInput q full command) containing clock before).heap address =
      logicalHeap q capWords before.heap address
  prefix_table : ∀ clock ≤ tailClock q (treeSize q full), ∀ address < tableWords full.length q (treeSize q full),
    logicalHeap q capWords (packingRun (callInput q full command) containing clock before).heap address =
      logicalHeap q capWords before.heap address
  trace : (packingDynamicTrace (callInput q full command) containing (tailClock q (treeSize q full)) before).length ≤
    14000 * ((q + 1) * treeSize q full)

theorem complete_of_data {bits q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (capWords heapWords : Nat) (containing : List PackingOp) (before after : WordState bits)
    (post : TailData full command configuration stage hq capWords heapWords origin containing before after)
    (hb : 0 < bits) (ht : 0 < treeSize q full)
    (hscalar : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q))
    (htable : tableWords full.length q (treeSize q full) ≤ capWords) :
    TailComplete full command configuration stage hq capWords heapWords origin containing before after := by
  let rom := callInput q full command
  let TR := PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full)
  let S := PA17A19RuntimeSelect009.coreSteps (treeSize q full)
  let ranked := packingRun rom containing TR before
  let selected := packingRun rom containing (TR + S) before
  let W := PSTRQueryLayout.physicalWorkspace full capWords bits
  let H := PSTRQueryLayout.header W (treeSize q full)
  let E := PSTRQueryLayout.endpoint W (treeSize q full) q
  have restRanks (clock : Nat) (hc : TR ≤ clock) :
      packingRun rom containing clock before = packingRun rom containing (clock - TR) ranked := by
    conv_lhs => rw [show clock = TR + (clock - TR) by omega]
    exact run_add rom containing TR (clock - TR) before
  have restSelector (clock : Nat) (hc : TR + S ≤ clock) :
      packingRun rom containing clock before = packingRun rom containing (clock - (TR + S)) selected := by
    conv_lhs => rw [show clock = (TR + S) + (clock - (TR + S)) by omega]
    exact run_add rom containing (TR + S) (clock - (TR + S)) before
  have hselected : selected = packingRun rom containing S ranked := run_add rom containing TR S before
  have hsmall : Fits bits (H + 16) := by
    apply (show H + 16 ≤ E from ?_).trans_lt hroom
    dsimp only [E, H, PSTRQueryLayout.endpoint, PSTRQueryLayout.childBase, PSTRQueryLayout.badFlags, PSTRQueryLayout.goodFlags]
    omega
  have hlowfit (physical : Nat) (hp : physical < H + 4) : Fits bits physical :=
    (hp.trans (by omega : H + 4 < H + 16)).trans hsmall
  have low : ∀ clock ≤ tailClock q (treeSize q full), ∀ physical < H + 4,
      (packingRun rom containing clock before).heap (BitVec.ofNat bits physical) = before.heap (BitVec.ofNat bits physical) := by
    intro clock hc physical hp
    by_cases htr : clock ≤ TR
    · exact post.leading clock htr physical hp
    · by_cases hs : clock ≤ TR + S
      · rw [restRanks clock (by omega)]
        exact (post.selector.frame (clock - TR) (by omega) physical (hlowfit physical hp)
          (.inl (show physical < H + 8 from by omega))).trans
          (post.leading TR le_rfl physical hp)
      · rw [restSelector clock (by omega), post.footer.prefix_heap (clock - (TR + S))
          (by change clock ≤ TR + S + 32 at hc; omega)]
        change selected.heap (BitVec.ofNat bits physical) = before.heap (BitVec.ofNat bits physical)
        rw [hselected]
        exact (post.selector.frame S le_rfl physical (hlowfit physical hp)
          (.inl (show physical < H + 8 from by omega))).trans
          (post.leading TR le_rfl physical hp)
  have high : ∀ clock ≤ tailClock q (treeSize q full), PA17A19RuntimeTests010.HighFrame E
      before.heap (packingRun rom containing clock before).heap := by
    intro clock hc
    by_cases htr : clock ≤ TR
    · exact post.ranks.prefix_high clock htr
    · by_cases hs : clock ≤ TR + S
      · rw [restRanks clock (by omega)]
        apply (post.ranks.prefix_high TR le_rfl).trans
        intro physical hf hge
        exact post.selector.frame (clock - TR) (by omega) physical hf (.inr hge)
      · rw [restSelector clock (by omega), post.footer.prefix_heap (clock - (TR + S))
          (by change clock ≤ TR + S + 32 at hc; omega)]
        change PA17A19RuntimeTests010.HighFrame E before.heap selected.heap
        rw [hselected]
        apply (post.ranks.prefix_high TR le_rfl).trans
        intro physical hf hge
        exact post.selector.frame S le_rfl physical hf (.inr hge)
  have logical : ∀ clock ≤ tailClock q (treeSize q full), ∀ address,
      address < PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + 4 →
      logicalHeap q capWords (packingRun rom containing clock before).heap address = logicalHeap q capWords before.heap address := by
    intro clock hc address ha
    exact logical_leading_four_frame full capWords (treeSize q full) before.heap _ hb hq hscalar hsmall (low clock hc) address ha
  have cap : ∀ clock ≤ tailClock q (treeSize q full), ∀ address < capWords,
      logicalHeap q capWords (packingRun rom containing clock before).heap address = logicalHeap q capWords before.heap address := by
    intro clock hc address ha
    apply logical clock hc address
    dsimp only [PSTRQueryLayout.header, PSTRQueryLayout.parentsBase, PSTRQueryLayout.countsBase, PSTRQueryLayout.logicalWorkspace]
    omega
  refine ⟨post, post.footer.correct, post.footer.active, ?_, post.footer.header, ?_, ?_, low, high, logical, cap, ?_, ?_⟩
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using post.footer.pc
  · intro clock hc
    by_cases htr : clock < TR
    · exact post.ranks.prefix_safe clock htr
    · by_cases hs : clock < TR + S
      · rw [restRanks clock (by omega)]
        exact post.selector.prefix_safe (clock - TR) (by omega)
      · rw [restSelector clock (by omega)]
        exact post.footer.prefix_safe (clock - (TR + S)) (by change clock < TR + S + 32 at hc; omega)
  · intro clock hc
    by_cases htr : clock ≤ TR
    · exact post.ranks.prefix_represents clock htr
    · by_cases hs : clock ≤ TR + S
      · rw [restRanks clock (by omega)]
        exact post.selector.prefix_represents (clock - TR) (by omega)
      · rw [restSelector clock (by omega)]
        exact post.footer.prefix_represents (clock - (TR + S)) (by change clock ≤ TR + S + 32 at hc; omega)
  · intro clock hc address ha
    exact cap clock hc address (ha.trans_le htable)
  · have trace := packingDynamicTrace_length_le rom containing (tailClock q (treeSize q full)) before
    have clockBound := tailClock_bound q (treeSize q full) ht
    change (packingDynamicTrace rom containing (tailClock q (treeSize q full)) before).length ≤
      14000 * ((q + 1) * treeSize q full)
    omega

theorem actual_tail_complete_8192 {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (hq : 0 < q) (hl : LaminarSchedule full) (containing : List PackingOp) :
    let bits := indexWidth 32 full.length q
    let C := capacityWords 8192 full.length q (treeSize q full)
    let words := physicalHeaderWords + packedCapacityWords q C bits + 8192 * (full.length + q + treeSize q full + 1)
    let W := PSTRQueryLayout.physicalWorkspace full C bits
    let H := PSTRQueryLayout.header W (treeSize q full)
    let L := PSTRQueryLayout.logicalWorkspace full C
    let cache := (prepareNormalization q full).indexed
    let counts := IndexedDescent.usedCounts cache configuration.used
    let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
    let node := PA17QueryBudget015.node full hq stage
    ∀ (_ : PA17A19RuntimeTests010.Embedded bits origin containing)
      (_ : PA17A19RuntimeRanks008.Embedded bits (origin + 355) containing)
      (_ : PA17A19RuntimeSelect009.CoreEmbedded bits (origin + 406) containing)
      (_ : PA17A19RuntimeReply016.Embedded bits (origin + 687) containing) (state : WordState bits),
    HeapRepresents q full C configuration state.heap →
    state.heap (BitVec.ofNat bits (W + 12)) = BitVec.ofNat bits (CapacityBits.width q) →
    state.heap (BitVec.ofNat bits (W + 13)) = lowMask bits (CapacityBits.width q) →
    state.register .address = BitVec.ofNat bits H → state.pc = BitVec.ofNat bits (5 * origin) → state.halted = false →
    PA17QueryTests009.Inputs cache (PSTRQueryLayout.header L (treeSize q full))
      (PSTRQueryLayout.countsBase L) (PSTRQueryLayout.parentsBase L (treeSize q full))
      (PSTRQueryLayout.header L (treeSize q full) + 1) (PA17A19RuntimeHeader011.row full stage)
      counts row node (logicalHeap q C state.heap) →
    state.heap (BitVec.ofNat bits (H + 2)) = BitVec.ofNat bits (PA17QueryHeader009.active full.length stage.val) →
    TailComplete full command configuration stage hq C words origin containing state
      (packingRun (callInput q full command) containing (tailClock q (treeSize q full)) state) := by
  dsimp only
  intro emTests emRanks emSelector emFooter state rep hwidth hmask hh hp ha hi hactiveCell
  let C := capacityWords 8192 full.length q (treeSize q full)
  have data := actual_tail_8192 full command configuration stage hq hl containing
    emTests emRanks emSelector emFooter state rep hwidth hmask hh hp ha hi hactiveCell
  have room := PA17A19RuntimeReply016.original_room full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have ht : 0 < treeSize q full := by
    let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    have hpositive : 0 < (prepareNormalization q full).indexed.nodes.size :=
      Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
    simpa only [treeSize, ne_of_gt hq, ite_false] using hpositive
  have htable : tableWords full.length q (treeSize q full) ≤ C := by
    simp only [C, capacityWords, ne_of_gt hq, ite_false]
    omega
  exact complete_of_data full command configuration stage hq C _ containing state _ data
    (PA17PackingBounds043.bits_pos full.length q) ht
    (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) room.1 htable
end PaperProofs.Structure.LaminarTree.PA17A19RuntimeQuery026

