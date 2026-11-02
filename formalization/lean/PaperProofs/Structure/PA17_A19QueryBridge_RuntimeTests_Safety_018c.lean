module
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Safety_018b
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010q

/-! The three actual cached-reader kernels, including the genuine loop back
jumps. Local accesses are the frozen proofs for their executed instructions. -/
@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeTests010
open PA17A19RuntimeTestsAccess017

theorem budgetInit_safe {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords rowBase budget : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16 < heapWords)
    (ready : BudgetCoreReady full configuration capWords (origin + 12) state)
    (htotal : state.register .total = BitVec.ofNat bits (budget + 1))
    (hrow : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))) =
      BitVec.ofNat bits rowBase)
    (hscalar : rowBase + budget * (treeSize q full + 1) < capWords)
    (count : Nat) (hc : count < 86) :
    StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing count state) := by
  exact straight_phase_safe em _ heapWords (beforeBudgetInit origin) budgetInit
    (counterTest 9 (5 * (origin + 196)) ++ nodeBody origin ++ afterNode origin)
    (by simpa only [beforeNodeTest, beforeBudgetInit, List.append_assoc] using nodeTest_partition origin)
    budgetInit_straight state (by simpa only [beforeBudgetInit_length] using ready.pc_eq) ready.active
    (budgetInit_access full command configuration capWords heapWords rowBase budget state hb hq hw
      ready.rep bitmap hs hf halloc ready.width ready.mask ready.header htotal hrow hscalar) count hc

theorem nodeBody_safe {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase remaining : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16 < heapWords)
    (ready : BudgetCoreReady full configuration capWords (origin + 103) state)
    (htotal : state.register .total = BitVec.ofNat bits (remaining + 1))
    (hrow : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
      BitVec.ofNat bits entryBase)
    (hr : remaining < treeSize q full) (hscalar : entryBase + 1 + remaining < capWords)
    (count : Nat) (hc : count < 93) :
    StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing count state) := by
  have access : ∀ cut (hcut : cut < (nodeBody origin).length),
      packingAccessFits (callInput q full command) heapWords
        (executeOps (callInput q full command) ((nodeBody origin).take cut) state) (nodeBody origin)[cut] := by
    rw [nodeBody_as_kernel]
    exact PA17A19RuntimeRead007.access_append _ heapWords nodeKernel (back (5 * (origin + 98))) state
      (nodeKernel_access full command configuration capWords heapWords entryBase remaining state hb hq hw
        ready.rep bitmap hs hf halloc ready.width ready.mask ready.header htotal hrow hr hscalar)
      (back_access _ _ heapWords _)
  exact branch_phase_safe em _ heapWords (beforeNode origin) (nodeBodyLead origin) (afterNode origin)
    (.jumpIfZero .fresh .old) (node_partition origin) (nodeBodyLead_straight origin) state
    (by simpa only [beforeNode_length] using ready.pc_eq) ready.active access count hc

theorem ancestorBody_safe {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase remaining encoded : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16 < heapWords)
    (ready : BudgetCoreReady full configuration capWords (origin + 227) state)
    (htotal : state.register .total = BitVec.ofNat bits (remaining + 1))
    (hrow : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
      BitVec.ofNat bits entryBase)
    (hnode : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 11)) =
      BitVec.ofNat bits encoded)
    (hr : remaining < treeSize q full) (hn : encoded ≤ treeSize q full)
    (hscalar : entryBase + 1 + (encoded - 1) < capWords)
    (count : Nat) (hc : count < 112) :
    StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing count state) := by
  have access : ∀ cut (hcut : cut < (ancestorBody origin).length),
      packingAccessFits (callInput q full command) heapWords
        (executeOps (callInput q full command) ((ancestorBody origin).take cut) state) (ancestorBody origin)[cut] := by
    rw [ancestorBody_as_kernel]
    exact PA17A19RuntimeRead007.access_append _ heapWords ancestorKernel (back (5 * (origin + 222))) state
      (ancestorKernel_access full command configuration capWords heapWords entryBase remaining encoded state
        hb hq hw ready.rep bitmap hs hf halloc ready.width ready.mask ready.header htotal hrow hnode hr hn hscalar)
      (back_access _ _ heapWords _)
  exact branch_phase_safe em _ heapWords (beforeAncestor origin) (ancestorBodyLead origin) (budgetFooter origin)
    (.jumpIfZero .fresh .old) (ancestor_partition origin) (ancestorBodyLead_straight origin) state
    (by simpa only [beforeAncestor_length] using ready.pc_eq) ready.active access count hc

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
