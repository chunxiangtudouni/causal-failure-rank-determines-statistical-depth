module
public import Structure.PA17_A19QueryBridge_RuntimeReplyCorrect_022c
public import Structure.PA17_A19QueryBridge_RuntimeTests_Semantics_019e

/-! Original callback correctness of the real readonly32-op footer at the
shared F8192/word32 allocation. Header/tool facts are actual same-call outputs. -/
@[expose] public section
set_option maxRecDepth 28000
set_option maxHeartbeats 2800000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

structure CallbackFooterPost {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (stage : Fin (full.length + 1))
    (capWords heapWords origin : Nat) (containing : List PackingOp) (before after : WordState bits) : Prop where
  correct : ReplyCorrect q (callback q full stage configuration.used) (replyState q capWords after)
  active : after.halted = false
  pc : after.pc = BitVec.ofNat bits (5 * (origin + 32))
  header : after.register .address = BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
  heap_eq : after.heap = before.heap
  prefix_safe : ∀ clock < 32, PA17A19RuntimeTestsSafety018.StepSafe (callInput q full command) containing heapWords
    (packingRun (callInput q full command) containing clock before)
  prefix_heap : ∀ clock ≤ 32, (packingRun (callInput q full command) containing clock before).heap = before.heap
  prefix_represents : ∀ clock ≤ 32, HeapRepresents q full capWords configuration
    (packingRun (callInput q full command) containing clock before).heap
  prefix_high : ∀ clock ≤ 32, PA17A19RuntimeTests010.HighFrame
    (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q)
    before.heap (packingRun (callInput q full command) containing clock before).heap
  trace : (packingDynamicTrace (callInput q full command) containing 32 before).length ≤ 384

theorem actual_callback_reply_8192 {q origin : Nat} (full : List (Finset (Fin q)))
    (command : Command) (configuration : Configuration q) (stage : Fin (full.length + 1))
    (hq : 0 < q) (hl : LaminarSchedule full) (containing : List PackingOp) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords 8192 full.length q (treeSize q full)
    let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits + 8192 * (full.length + q + treeSize q full + 1)
    let W := PSTRQueryLayout.physicalWorkspace full capWords bits
    let H := PSTRQueryLayout.header W (treeSize q full)
    let cache := (prepareNormalization q full).indexed
    let leaves := IndexedDescent.leafTools cache
    let counts := IndexedDescent.usedCounts cache configuration.used
    let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
    let node := PA17QueryBudget015.node full hq stage
    let active := PA17QueryHeader009.active full.length stage.val
    let g := PA17QueryRanks011.firstFalseValue q (fun budget => IndexedQuery.accepts cache counts (IndexedQuery.entryAt row budget))
    let b := PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node)
    ∀ (_ : PA17A19RuntimeReply016.Embedded bits origin containing) (state : WordState bits),
    HeapRepresents q full capWords configuration state.heap →
    state.register .address = BitVec.ofNat bits H → state.pc = BitVec.ofNat bits (5 * origin) → state.halted = false →
    state.heap (BitVec.ofNat bits (H + 2)) = BitVec.ofNat bits active →
    state.heap (BitVec.ofNat bits (H + 4)) = BitVec.ofNat bits g →
    state.heap (BitVec.ofNat bits (H + 5)) = BitVec.ofNat bits b →
    state.heap (BitVec.ofNat bits (H + 7)) = BitVec.ofNat bits (if active = 0 then 0 else if b = 0 then 0 else 1) →
    ((state.heap (BitVec.ofNat bits (H + 7))).toNat ≠ 0 →
      state.heap (BitVec.ofNat bits (PSTRQueryLayout.childBase W (treeSize q full) q + treeSize q full + 2)) =
        BitVec.ofNat bits (PA17QueryReply017.encodeTool
          (IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row (b - 1))))) →
    CallbackFooterPost full command configuration stage capWords heapWords origin containing state
      (packingRun (callInput q full command) containing 32 state) := by
  dsimp only
  intro em state rep hh hp ha hactiveCell hgood hbad hflag htool
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let W := PSTRQueryLayout.physicalWorkspace full capWords bits
  let H := PSTRQueryLayout.header W (treeSize q full)
  let rom := callInput q full command
  let cache := (prepareNormalization q full).indexed
  let leaves := IndexedDescent.leafTools cache
  let counts := IndexedDescent.usedCounts cache configuration.used
  let row := IndexedQuery.storedPositiveRow q full (PA17QueryBudget015.rowIndex full stage)
  let node := PA17QueryBudget015.node full hq stage
  let active := PA17QueryHeader009.active full.length stage.val
  let b := PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node)
  let enabled := if active = 0 then 0 else if b = 0 then 0 else 1
  have room := PA17A19RuntimeReply016.original_room full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have hqRoom : q + 3 ≤ PSTRQueryLayout.endpoint W (treeSize q full) q := by
    unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega
  have h1fit : Fits bits 1 := (show 1 < PSTRQueryLayout.endpoint W (treeSize q full) q by omega).trans room.1
  have hactiveBound : active ≤ 1 := by unfold active PA17QueryHeader009.active; split_ifs <;> omega
  have hactive : (state.heap (BitVec.ofNat bits (H + 2))).toNat = active := by
    rw [hactiveCell, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hactiveBound.trans_lt h1fit)]
  have hEnabledBound : enabled ≤ 1 := by unfold enabled; split_ifs <;> omega
  have hEnabledNat : (state.heap (BitVec.ofNat bits (H + 7))).toNat = enabled := by
    rw [hflag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hEnabledBound.trans_lt h1fit)]
  have hflagActual : state.heap (BitVec.ofNat bits (H + 7)) =
      BitVec.ofNat bits (if (state.heap (BitVec.ofNat bits (H + 2))).toNat = 0 then 0 else if b = 0 then 0 else 1) := by
    rw [hactive]
    exact hflag
  have htoolActual : (if (state.heap (BitVec.ofNat bits (H + 2))).toNat = 0 then 0 else if b = 0 then 0 else 1) ≠ 0 →
      state.heap (BitVec.ofNat bits (PSTRQueryLayout.childBase W (treeSize q full) q + treeSize q full + 2)) =
        BitVec.ofNat bits (PA17QueryReply017.encodeTool (IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row (b - 1)))) := by
    intro henabled
    apply htool
    rw [hEnabledNat]
    simpa only [hactive] using henabled
  have result := actual_query_reply_correct em rom cache leaves counts row node capWords W (treeSize q full) state
    room.1 (by rfl) rep.1 hh hp ha hgood hbad hflagActual htoolActual
  have correct : ReplyCorrect q (callback q full stage configuration.used)
      (replyState q capWords (packingRun rom containing 32 state)) := by
    rw [callback_eq_original_query full stage configuration.used hq]
    have hc := result.2
    change ReplyCorrect q (if (state.heap (BitVec.ofNat bits (H + 2))).toNat = 0 then IndexedQuery.terminalReply q else
      IndexedQuery.query cache leaves counts row node) (replyState q capWords (packingRun rom containing 32 state)) at hc
    rw [hactive] at hc
    exact hc
  refine ⟨correct, result.1.active, result.1.pc, result.1.header, result.1.heap_eq, ?_, result.1.prefix_heap, ?_, ?_, result.1.trace⟩
  · intro clock hc
    exact PA17A19RuntimeReply016.original_prefix_decoded full command configuration 8192 8192
      (by decide) (by decide) (by decide) hq hl containing em state rep hh hp ha clock hc
  · intro clock hc
    rw [result.1.prefix_heap clock hc]
    exact rep
  · intro clock hc physical _ _
    rw [result.1.prefix_heap clock hc]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022
