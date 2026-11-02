module

public import Structure.PA17_A19QueryBridge_RuntimeQuery_026a
public import Structure.PA17_A19QueryBridge_RuntimeSelect_Input_025c
public import Structure.PA17_A19QueryBridge_RuntimeReplyCorrect_022f
public import Structure.PA17_A19QueryBridge_RuntimeReplyCorrect_022d

/-! One containing run executes the real Tests355,Ranks51,selector281 and
footer32 blocks. The intermediate states are actual runs,without reset or
free register/heap copies. Payload semantics use the selector-entry snapshot. -/

@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeQuery026

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def tailClock (q size : Nat) : Nat :=
  PA17A19RuntimeTestsSemantics019.testsRanksClock q size + PA17A19RuntimeSelect009.coreSteps size + 32

structure SelectorPost {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (capWords heapWords origin : Nat) (containing : List PackingOp)
    (node : Option (prepareNormalization q full).indexed.NodeId)
    (before after : WordState bits) : Prop where
  active : after.halted = false
  pc : after.pc = BitVec.ofNat bits (5 * (origin + 281))
  header : after.register .address = BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
  tool :
    let cache := (prepareNormalization q full).indexed
    let counts := IndexedDescent.usedCounts cache configuration.used
    let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
    let b := PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node)
    let H := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
    after.heap (BitVec.ofNat bits (PA17A19RuntimeSelect009.toolSlot H q (treeSize q full))) =
      BitVec.ofNat bits (PA17LeafLabels005.encodeTool
        (node.bind (IndexedDescent.selectAt cache (IndexedDescent.leafTools cache) counts
          (PA17A19RuntimeSelectInput025.actualPayloadCapacity full capWords
            (PA17A19RuntimeHeader011.row full stage) (b - 1) before.heap))))
  prefix_safe : ∀ clock < PA17A19RuntimeSelect009.coreSteps (treeSize q full),
    PA17A19RuntimeTestsSafety018.StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing clock before)
  frame : ∀ clock ≤ PA17A19RuntimeSelect009.coreSteps (treeSize q full), ∀ physical,
    Fits bits physical →
      (physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8 ∨
        PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q ≤ physical) →
      (packingRun (callInput q full command) containing clock before).heap (BitVec.ofNat bits physical) =
        before.heap (BitVec.ofNat bits physical)
  prefix_represents : ∀ clock ≤ PA17A19RuntimeSelect009.coreSteps (treeSize q full),
    HeapRepresents q full capWords configuration (packingRun (callInput q full command) containing clock before).heap
  trace : (packingDynamicTrace (callInput q full command) containing
    (PA17A19RuntimeSelect009.coreSteps (treeSize q full)) before).length ≤ 3600 * (treeSize q full + 1)

structure TailData {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1)) (hq : 0 < q)
    (capWords heapWords origin : Nat) (containing : List PackingOp)
    (before after : WordState bits) : Prop where
  ranks :
    let cache := (prepareNormalization q full).indexed
    let counts := IndexedDescent.usedCounts cache configuration.used
    let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
    let node := PA17QueryBudget015.node full hq stage
    let g := PA17QueryRanks011.firstFalseValue q (fun budget => IndexedQuery.accepts cache counts (IndexedQuery.entryAt row budget))
    let b := PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node)
    PA17A19RuntimeTestsSemantics019.TestsRanksPost full command configuration capWords heapWords
      (PA17A19RuntimeHeader011.row full stage) origin containing counts row node g b
      (PA17QueryHeader009.active full.length stage.val) before
      (packingRun (callInput q full command) containing (PA17A19RuntimeTests010.steps q (treeSize q full)) before)
      (packingRun (callInput q full command) containing (PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full)) before)
  leading : ∀ clock ≤ PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full), ∀ physical,
    physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 4 →
      (packingRun (callInput q full command) containing clock before).heap (BitVec.ofNat bits physical) =
        before.heap (BitVec.ofNat bits physical)
  selector : SelectorPost full command configuration stage capWords heapWords (origin + 406) containing
    (PA17QueryBudget015.node full hq stage)
    (packingRun (callInput q full command) containing (PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full)) before)
    (packingRun (callInput q full command) containing
      (PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full) + PA17A19RuntimeSelect009.coreSteps (treeSize q full)) before)
  footer : PA17A19RuntimeReplyCorrect022.CallbackFooterPost full command configuration stage capWords heapWords
    (origin + 687) containing
    (packingRun (callInput q full command) containing
      (PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full) + PA17A19RuntimeSelect009.coreSteps (treeSize q full)) before) after

theorem actual_tail_8192 {q origin : Nat} (full : List (Finset (Fin q))) (command : Command)
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
    TailData full command configuration stage hq C words origin containing state
      (packingRun (callInput q full command) containing (tailClock q (treeSize q full)) state) := by
  dsimp only
  intro emTests emRanks emSelector emFooter state rep hwidth hmask hh hp ha hi hactiveCell
  let bits := indexWidth 32 full.length q
  let C := capacityWords 8192 full.length q (treeSize q full)
  let words := physicalHeaderWords + packedCapacityWords q C bits + 8192 * (full.length + q + treeSize q full + 1)
  let W := PSTRQueryLayout.physicalWorkspace full C bits
  let H := PSTRQueryLayout.header W (treeSize q full)
  let cache := (prepareNormalization q full).indexed
  let leaves := IndexedDescent.leafTools cache
  let counts := IndexedDescent.usedCounts cache configuration.used
  let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
  let node := PA17QueryBudget015.node full hq stage
  let rowBase := PA17A19RuntimeHeader011.row full stage
  let active := PA17QueryHeader009.active full.length stage.val
  let g := PA17QueryRanks011.firstFalseValue q (fun budget => IndexedQuery.accepts cache counts (IndexedQuery.entryAt row budget))
  let b := PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node)
  let rom := callInput q full command
  let TR := PA17A19RuntimeTestsSemantics019.testsRanksClock q (treeSize q full)
  let S := PA17A19RuntimeSelect009.coreSteps (treeSize q full)
  let ranked := packingRun rom containing TR state
  let selected := packingRun rom containing S ranked
  have rich := original_tests_ranks_inputs_8192 full command configuration stage hq hl containing
    emTests emRanks state rep hwidth hmask hh hp ha hi hactiveCell
  have tr := rich.1
  have leading := rich.2.1
  have hiRanked := rich.2.2
  have headerOffset (offset : Nat) (ho : offset ≤ 13) : W + offset < H + 4 := by
    dsimp only [H, PSTRQueryLayout.header, PSTRQueryLayout.parentsBase, PSTRQueryLayout.countsBase]
    omega
  have hwidthRanked : ranked.heap (BitVec.ofNat bits (W + 12)) = BitVec.ofNat bits (CapacityBits.width q) :=
    (leading TR le_rfl (W + 12) (headerOffset 12 (by decide))).trans hwidth
  have hmaskRanked : ranked.heap (BitVec.ofNat bits (W + 13)) = lowMask bits (CapacityBits.width q) :=
    (leading TR le_rfl (W + 13) (headerOffset 13 (by decide))).trans hmask
  have hactiveRanked : ranked.heap (BitVec.ofNat bits (H + 2)) = BitVec.ofNat bits active :=
    (leading TR le_rfl (H + 2) (by change H + 2 < H + 4; omega)).trans hactiveCell
  have repRanked : HeapRepresents q full C configuration ranked.heap := tr.prefix_represents TR le_rfl
  have raw := PA17A19RuntimeSelectInput025.actual_original_selector full command configuration stage hq hl containing
    emSelector ranked repRanked hwidthRanked hmaskRanked tr.header tr.pc tr.active hiRanked tr.budget
  rcases raw with ⟨sactive, spc, sheader, stool, ssafe, sframe, srep, strace⟩
  have selector : SelectorPost full command configuration stage C words (origin + 406) containing node ranked selected := by
    refine ⟨sactive, spc, sheader, stool, ssafe, ?_, srep, strace⟩
    intro clock hc physical hf hprotect
    apply sframe clock hc physical hf
    simpa only [PA17A19RuntimeSelectInput025.endpoint_layout] using hprotect
  have room := PA17A19RuntimeReply016.original_room full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have hcell (offset : Nat) (ho : offset < 8) : selected.heap (BitVec.ofNat bits (H + offset)) =
      ranked.heap (BitVec.ofNat bits (H + offset)) := by
    apply selector.frame S le_rfl (H + offset)
    · apply (show H + offset < PSTRQueryLayout.endpoint W (treeSize q full) q from ?_).trans room.1
      dsimp only [H, PSTRQueryLayout.endpoint, PSTRQueryLayout.childBase, PSTRQueryLayout.badFlags, PSTRQueryLayout.goodFlags]
      omega
    · exact .inl (show H + offset < H + 8 from by omega)
  have hactiveSelected : selected.heap (BitVec.ofNat bits (H + 2)) = BitVec.ofNat bits active :=
    (hcell 2 (by decide)).trans hactiveRanked
  have hgoodSelected : selected.heap (BitVec.ofNat bits (H + 4)) = BitVec.ofNat bits g :=
    (hcell 4 (by decide)).trans tr.good_rank
  have hbadSelected : selected.heap (BitVec.ofNat bits (H + 5)) = BitVec.ofNat bits b :=
    (hcell 5 (by decide)).trans tr.bad_rank
  have hflagSelected : selected.heap (BitVec.ofNat bits (H + 7)) =
      BitVec.ofNat bits (if active = 0 then 0 else if b = 0 then 0 else 1) :=
    (hcell 7 (by decide)).trans tr.mask
  have hs : cache.nodes.size = treeSize q full := by
    simp only [cache, treeSize, ne_of_gt hq, ite_false]
  let entryBase := rowBase + (b - 1) * (cache.nodes.size + 1)
  let payload := PA17A19RuntimeSelectInput025.actualPayloadCapacity full C rowBase (b - 1) ranked.heap
  have hentry : PA17TagBridge001.TagFirstRep cache (logicalHeap q C ranked.heap) entryBase
      (IndexedQuery.entryAt row (b - 1)) :=
    PA17A19RuntimeReplyCorrect022.inputs_selected_entry_rep cache _ _ _ _ rowBase counts row node _ hiRanked
  have hpayload : ∀ target : cache.NodeId,
      logicalHeap q C ranked.heap (entryBase + 1 + target.val) = payload.get target := by
    intro target
    rw [PA17A19RuntimeSelectInput025.actualPayloadCapacity_get]
    simp only [entryBase, PA17A19RuntimeSelectInput025.payloadBase, hs]
  have hslotCanonical := PA17A19RuntimeReplyCorrect022.enabled_raw_slot_canonical cache leaves counts row node
    (logicalHeap q C ranked.heap) entryBase payload active H
    (PA17A19RuntimeSelect009.toolSlot H q (treeSize q full)) selected hpayload hentry hflagSelected stool
  have htoolCoordinate : PA17A19RuntimeSelect009.toolSlot H q (treeSize q full) =
      PSTRQueryLayout.childBase W (treeSize q full) q + treeSize q full + 2 := by
    dsimp only [H, PA17A19RuntimeSelect009.toolSlot, PA17A19RuntimeSelect009.childBase,
      PSTRQueryLayout.childBase, PSTRQueryLayout.badFlags, PSTRQueryLayout.goodFlags]
    omega
  have htool : (selected.heap (BitVec.ofNat bits (H + 7))).toNat ≠ 0 →
      selected.heap (BitVec.ofNat bits (PSTRQueryLayout.childBase W (treeSize q full) q + treeSize q full + 2)) =
        BitVec.ofNat bits (PA17QueryReply017.encodeTool
          (IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row (b - 1)))) := by
    simpa only [htoolCoordinate] using hslotCanonical
  have footer := PA17A19RuntimeReplyCorrect022.actual_callback_reply_8192 full command configuration stage hq hl containing
    emFooter selected (selector.prefix_represents S le_rfl) selector.header
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using selector.pc) selector.active
    hactiveSelected hgoodSelected hbadSelected hflagSelected htool
  have hselected : packingRun rom containing (TR + S) state = selected := run_add rom containing TR S state
  have hfinal : packingRun rom containing (tailClock q (treeSize q full)) state =
      packingRun rom containing 32 selected := by
    unfold tailClock
    rw [run_add, run_add]
  refine ⟨tr, leading, ?_, ?_⟩
  · rw [hselected]
    exact selector
  · rw [hselected, hfinal]
    exact footer

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeQuery026
