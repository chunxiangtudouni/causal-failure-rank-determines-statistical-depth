module
public import Structure.PA17_A19QueryBridge_RuntimeTests_Control_015h
public import Structure.PA17_A19QueryBridge_RuntimeTests_Control_015m

/-! Every actual outer-loop clock preserves the exact complement of scratch
H8..14 and the budgets written by that loop. Concrete q body/phase producers
are called directly, never supplied by an original caller. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def OuterFrame {bits q : Nat} (full : List (Finset (Fin q))) (capWords remaining : Nat)
    (old fresh : BitVec bits → BitVec bits) : Prop :=
 ∀ address,
    (∀ offset, 8 ≤ offset → offset ≤ 14 → address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + offset)) →
    (∀ budget < remaining,
      address ≠ BitVec.ofNat bits
        (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 + budget) ∧
      address ≠ BitVec.ofNat bits
        (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 + (q + 2) + budget)) →
      fresh address = old address

theorem actual_budgetLoop_prefix_frame {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords rowBase remaining encoded : Nat)
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
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 7))) (ha : state.halted = false)
    (hcounter : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8)) =
      BitVec.ofNat bits remaining)
    (hrowPointer : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))) =
      BitVec.ofNat bits rowBase)
    (hnodePointer : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 1)) =
      BitVec.ofNat bits encoded)
    (hremaining : remaining ≤ q + 2) (hencoded : encoded ≤ treeSize q full)
    (hrowExtent : rowBase + (q + 2) * (treeSize q full + 1) ≤ capWords)
    (hparents : ∀ e ≤ treeSize q full, logicalHeap q capWords state.heap
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full)
    (count : Nat) (hcut : count ≤ outerClock (treeSize q full) remaining) :
    OuterFrame full capWords remaining state.heap
      (packingRun (callInput q full command) containing count state).heap := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let endpoint := PSTRQueryLayout.endpoint workspace (treeSize q full) q
  have hend : Fits bits endpoint := hendpoint_alloc.trans_lt hf
  have hroom : Fits bits (header + 16) := (show header + 16 < endpoint by
    unfold endpoint PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega).trans hend
  have hqfit : Fits bits (q + 2) := (show q + 2 ≤ endpoint by
    unfold endpoint PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega).trans_lt hend
  have wordNe (left right : Nat) (hl : left < endpoint) (hr : right < endpoint) (hne : left ≠ right) :
      BitVec.ofNat bits left ≠ BitVec.ofNat bits right := by
    intro heq
    exact hne ((ofNat_injective_of_fit left right (hl.trans hend) (hr.trans hend)).mp heq)
  induction remaining generalizing state count with
  | zero =>
    intro address _ _
    have htest : count ≤ 5 := by simpa only [outerClock, Nat.zero_mul, Nat.add_zero] using hcut
    rw [actual_budgetTest_prefix em rom state hp ha count htest]
    apply congrFun (executeOps_prefix_noStore rom (counterTest 8 (5 * (origin + 355))) state ?_ count) address
    simp [counterTest, counterLead, loadSlot, HeapPreservingOp]
  | succ remaining ih =>
    let test := packingRun rom containing 5 state
    let body := packingRun rom containing (budgetBlockClock (treeSize q full)) test
    have ht := actual_budgetTest em rom header (remaining + 1) state hp ha hh hcounter
      ((show remaining + 1 ≤ q + 2 by omega).trans_lt hqfit)
    have htpc : test.pc = BitVec.ofNat bits (5 * (origin + 12)) := by
      simpa only [show remaining + 1 ≠ 0 by omega, ite_false] using ht.2.2.2.1
    have htheap : test.heap = state.heap := ht.2.2.1
    have block := actual_budget_block em full command configuration capWords heapWords rowBase remaining encoded test
      hb hq hw (by rw [htheap]; exact rep) bitmap hs hf hendpoint_alloc
      (by rw [htheap]; exact hwidth) (by rw [htheap]; exact hmask) ht.2.1 htpc ht.2.2.2.2 ht.1
      (by rw [htheap]; exact hrowPointer) (by rw [htheap]; exact hnodePointer)
      (by omega) hencoded hrowExtent (by rw [htheap]; exact hparents)
    have hbodyFrame : ∀ physical < header + 8, body.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
      intro physical hphysical
      exact (block.leading physical hphysical).trans (congrFun htheap _)
    have hbodyHigh : HighFrame endpoint state.heap body.heap := by
      intro physical hphysical hge
      exact (block.high physical hphysical hge).trans (congrFun htheap _)
    have hrepBody := represents_of_leading_frame full configuration capWords state.heap body.heap
      (by omega) hq rep bitmap hs hroom hbodyFrame
    have hcache (offset : Nat) (ho : offset ≤ 13) : workspace + offset < header + 8 := by
      unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      omega
    have hwidthBody := (hbodyFrame _ (hcache 12 (by decide))).trans hwidth
    have hmaskBody := (hbodyFrame _ (hcache 13 (by decide))).trans hmask
    have hrowBody := (hbodyFrame header (by omega)).trans hrowPointer
    have hnodeBody := (hbodyFrame (header + 1) (by omega)).trans hnodePointer
    have hlogical := logical_leading_frame full capWords (treeSize q full) state.heap body.heap
      (by omega) hq hs hroom hbodyFrame
    have hparentsBody : ∀ e ≤ treeSize q full, logicalHeap q capWords body.heap
        (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full := by
      intro e he
      rw [hlogical _ (by unfold PSTRQueryLayout.header; omega)]
      exact hparents e he
    intro address hscratch hflags
    by_cases htest : count ≤ 5
    · rw [actual_budgetTest_prefix em rom state hp ha count htest]
      apply congrFun (executeOps_prefix_noStore rom (counterTest 8 (5 * (origin + 355))) state ?_ count) address
      simp [counterTest, counterLead, loadSlot, HeapPreservingOp]
    · have hfront : packingRun rom containing count state = packingRun rom containing (count - 5) test := by
        conv_lhs => rw [show count = 5 + (count - 5) by omega]
        exact run_add rom containing 5 (count - 5) state
      rw [hfront]
      by_cases hbody : count - 5 ≤ budgetBlockClock (treeSize q full)
      · have hpref := actual_budget_block_prefix_frame em full command configuration capWords heapWords rowBase remaining encoded test
          hb hq hw (by rw [htheap]; exact rep) bitmap hs hf hendpoint_alloc
          (by rw [htheap]; exact hwidth) (by rw [htheap]; exact hmask) ht.2.1 htpc ht.2.2.2.2 ht.1
          (by rw [htheap]; exact hrowPointer) (by rw [htheap]; exact hnodePointer)
          (by omega) hencoded hrowExtent (by rw [htheap]; exact hparents) (count - 5) hbody
        exact (hpref address hscratch (hflags remaining (by omega)).1 (hflags remaining (by omega)).2).trans
          (congrFun htheap address)
      · have htail : packingRun rom containing (count - 5) test =
            packingRun rom containing (count - 5 - budgetBlockClock (treeSize q full)) body := by
          conv_lhs => rw [show count - 5 = budgetBlockClock (treeSize q full) +
            (count - 5 - budgetBlockClock (treeSize q full)) by omega]
          exact run_add rom containing (budgetBlockClock (treeSize q full))
            (count - 5 - budgetBlockClock (treeSize q full)) test
        rw [htail]
        have hi : OuterFrame full capWords remaining body.heap
            (packingRun rom containing (count - 5 - budgetBlockClock (treeSize q full)) body).heap := by
          apply ih body hrepBody hwidthBody hmaskBody block.header block.pc block.active block.counter
            hrowBody hnodeBody (by omega) hparentsBody (count - 5 - budgetBlockClock (treeSize q full))
          simp only [outerClock, Nat.add_mul, Nat.one_mul] at hcut ⊢
          omega
        exact (hi address hscratch (fun budget hbudget => hflags budget (by omega))).trans
          ((block.«outside» address hscratch (hflags remaining (by omega)).1 (hflags remaining (by omega)).2).trans
            (congrFun htheap address))

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
