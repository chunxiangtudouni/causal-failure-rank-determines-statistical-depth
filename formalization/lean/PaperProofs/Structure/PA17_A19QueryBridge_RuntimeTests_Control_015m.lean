module
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015j
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015l
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010q

/-! All actual clocks of the concrete budget body preserve its exact outside
write-set. Every phase readiness is produced by actual_budget_phases. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem actual_budget_block_prefix_frame {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords rowBase budget encoded : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hendpoint_alloc : PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) q ≤ heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (hh : state.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 12))) (ha : state.halted = false)
    (htotal : state.register .total = BitVec.ofNat bits (budget + 1))
    (hrowPointer : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))) =
      BitVec.ofNat bits rowBase)
    (hnodePointer : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 1)) =
      BitVec.ofNat bits encoded)
    (hbudget : budget < q + 2) (hencoded : encoded ≤ treeSize q full)
    (hrowExtent : rowBase + (q + 2) * (treeSize q full + 1) ≤ capWords)
    (hparents : ∀ e ≤ treeSize q full, logicalHeap q capWords state.heap
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full)
    (count : Nat) (hcut : count ≤ budgetBlockClock (treeSize q full)) :
    BudgetFrame full capWords budget state.heap
      (packingRun (callInput q full command) containing count state).heap := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let phases := budgetPhases rom containing (treeSize q full) state
  let entryBase := rowBase + budget * (treeSize q full + 1)
  have hend : Fits bits (PSTRQueryLayout.endpoint workspace (treeSize q full) q) := hendpoint_alloc.trans_lt hf
  have hroom : Fits bits (header + 16) := (show header + 16 < PSTRQueryLayout.endpoint workspace (treeSize q full) q by
    unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega).trans hend
  have halloc' : header + 16 < heapWords := by
    have hlt : header + 16 < PSTRQueryLayout.endpoint workspace (treeSize q full) q := by
      unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
      omega
    exact hlt.trans_le hendpoint_alloc
  have hentry : entryBase + (treeSize q full + 1) ≤ capWords := by
    have hm := Nat.mul_le_mul_right (treeSize q full + 1) (show budget + 1 ≤ q + 2 by omega)
    dsimp only [entryBase]
    nlinarith
  have ready := actual_budget_phases em full command configuration capWords heapWords rowBase budget encoded state
    hb hq hw rep bitmap hs hf hendpoint_alloc hwidth hmask hh hp ha htotal hrowPointer hnodePointer
    hbudget hencoded hrowExtent hparents
  intro address hscratch hgood hbad
  have oldEntry := ready.entry_frame address hscratch hgood hbad
  have oldNodes := ready.nodes_frame address hscratch hgood hbad
  have oldInitialized := ready.initialized_frame address hscratch hgood hbad
  have oldAncestors := ready.ancestors_frame address hscratch hgood hbad
  rw [actual_budget_prefix_split rom containing (treeSize q full) state count]
  split_ifs with h0 h1 h2 h3
  · exact actual_budgetInit_prefix_frame em full command configuration capWords heapWords rowBase budget state
      hb hq hw rep bitmap hs hf halloc' hwidth hmask hh htotal hrowPointer (by dsimp only [entryBase] at hentry; omega)
      hp ha address (hscratch 8 (by decide) (by decide)) (hscratch 9 (by decide) (by decide))
      (hscratch 10 (by decide) (by decide)) (hscratch 13 (by decide) (by decide)) count h0
  · change (packingRun rom containing (count - 86) phases.entry).heap address = state.heap address
    refine (actual_nodeLoop_prefix_frame em full command configuration capWords heapWords entryBase (treeSize q full) phases.entry
      hb hq hw ready.entry_core.rep bitmap hs hf halloc' hend ready.entry_core.width ready.entry_core.mask
      ready.entry_core.header ready.entry_core.pc_eq ready.entry_core.active ready.entry_counter ready.entry_row (by omega) hentry
      address (hscratch 9 (by decide) (by decide)) (hscratch 10 (by decide) (by decide)) (count - 86) ?_).trans oldEntry
    simpa only [nodeClock] using h1
  · change (packingRun rom containing (count - 86 - (5 + 98 * treeSize q full)) phases.nodes).heap address = state.heap address
    exact (actual_acceptFinish_prefix_frame em rom header budget phases.nodes ready.nodes_core.header ready.nodes_budget
      ready.nodes_core.pc_eq ready.nodes_core.active address hgood
      (hscratch 11 (by decide) (by decide)) (hscratch 14 (by decide) (by decide)) (hscratch 12 (by decide) (by decide))
      _ h2).trans oldNodes
  · change (packingRun rom containing (count - 86 - (5 + 98 * treeSize q full) - 26) phases.initialized).heap address = state.heap address
    exact (actual_ancestorLoop_prefix_frame em full command configuration capWords heapWords entryBase (treeSize q full) encoded phases.initialized
      hb hq hw ready.initialized_core.rep bitmap hs hf halloc' ready.initialized_core.width ready.initialized_core.mask
      ready.initialized_core.header ready.initialized_core.pc_eq ready.initialized_core.active ready.initialized_counter
      ready.initialized_row ready.initialized_node (by omega) hencoded hentry ready.initialized_parents address
      (hscratch 11 (by decide) (by decide)) (hscratch 12 (by decide) (by decide)) (hscratch 14 (by decide) (by decide))
      _ h3).trans oldInitialized
  · change (packingRun rom containing (count - 86 - (5 + 98 * treeSize q full) - 26 - ancestorClock (treeSize q full)) phases.ancestors).heap address = state.heap address
    refine (actual_budgetFooter_prefix_frame em rom header q budget phases.ancestors
      ((show 1 ≤ header + 16 by omega).trans_lt hroom) (by rfl)
      ready.ancestors_core.header ready.ancestors_budget ready.ancestors_core.pc_eq ready.ancestors_core.active address hbad _ ?_).trans oldAncestors
    simp only [budgetBlockClock, nodeClock, ancestorClock] at hcut h3 ⊢
    omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
