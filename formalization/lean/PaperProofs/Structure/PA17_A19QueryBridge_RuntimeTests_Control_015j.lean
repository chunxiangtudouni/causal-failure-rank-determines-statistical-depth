module
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015i

/-! Every actual node-loop clock preserves every Word cell outside H9/H10. -/
@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem actual_nodeLoop_prefix_frame {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase remaining : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16 < heapWords)
    (hend : Fits bits (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q))
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (hh : state.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 98))) (ha : state.halted = false)
    (hc : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 9)) =
      BitVec.ofNat bits remaining)
    (he : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
      BitVec.ofNat bits entryBase)
    (hr : remaining ≤ treeSize q full) (hrow : entryBase + (treeSize q full + 1) ≤ capWords)
    (address : BitVec bits)
    (h9 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 9))
    (h10 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 10))
    (count : Nat) (hcut : count ≤ nodeClock remaining) :
    (packingRun (callInput q full command) containing count state).heap address = state.heap address := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let logicalHeader := PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)
  let logicalCounts := PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  induction remaining generalizing state count with
  | zero =>
    have htest : count ≤ 5 := hcut
    rw [actual_nodeTest_prefix em rom state hp ha count htest]
    apply congrFun (executeOps_prefix_noStore rom (counterTest 9 (5 * (origin + 196))) state ?_ count) address
    simp [counterTest, counterLead, loadSlot, HeapPreservingOp]
  | succ remaining ih =>
    have hrfit : Fits bits (remaining + 1) := (show remaining + 1 ≤ header by
      unfold header PSTRQueryLayout.header; omega).trans_lt hheader
    let test := packingRun rom containing 5 state
    let body := packingRun rom containing 93 test
    let testBit := decide (logicalHeap q capWords state.heap (logicalCounts + remaining) ≤
      logicalHeap q capWords state.heap (entryBase + 1 + remaining))
    have ht := actual_nodeTest em rom header (remaining + 1) state hp ha hh hc hrfit
    have htpc : test.pc = BitVec.ofNat bits (5 * (origin + 103)) := by
      simpa only [show remaining + 1 ≠ 0 by omega, ite_false] using ht.2.2.2.1
    have htheap : test.heap = state.heap := ht.2.2.1
    have hk := nodeKernel_result full command configuration capWords heapWords entryBase remaining test hb hq hw
      (by rw [htheap]; exact rep) bitmap hs hf halloc
      (by rw [htheap]; exact hwidth) (by rw [htheap]; exact hmask) ht.2.1 ht.1
      (by rw [htheap]; exact he) (by omega) (by omega)
    have hbdy := actual_nodeBody_end em rom test htpc ht.2.2.2.2
    have hbodyHeap : body.heap = Function.update
        (Function.update state.heap (BitVec.ofNat bits (header + 9)) (BitVec.ofNat bits remaining))
        (BitVec.ofNat bits (header + 10)) (wordMask testBit (state.heap (BitVec.ofNat bits (header + 10)))) := by
      rw [hbdy.1, hk.1, htheap, ← logical_counts_word full capWords remaining state.heap hq]
      dsimp only [header, workspace, logicalCounts, testBit]
      by_cases hle : logicalHeap q capWords state.heap
          (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords) + remaining) ≤
          logicalHeap q capWords state.heap (entryBase + 1 + remaining)
      · simp [wordMask, hle]
      · simp [wordMask, hle]
    have hbodyAddress : body.register .address = BitVec.ofNat bits header := hbdy.2.1.trans hk.2
    have hslotNe (left right : Nat) (hl : left ≤ 16) (hr' : right ≤ 16) (hne : left ≠ right) :
        BitVec.ofNat bits (header + left) ≠ BitVec.ofNat bits (header + right) := by
      intro h
      exact hne ((slots_eq_iff header left right hroom hl hr').mp h)
    have hslot (offset : Nat) (ho : offset ≤ 16) (h9 : offset ≠ 9) (h10 : offset ≠ 10) :
        body.heap (BitVec.ofNat bits (header + offset)) = state.heap (BitVec.ofNat bits (header + offset)) := by
      rw [hbodyHeap, Function.update_of_ne (hslotNe offset 10 ho (by decide) h10),
        Function.update_of_ne (hslotNe offset 9 ho (by decide) h9)]
    have hbodyCounter : body.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits remaining := by
      rw [hbodyHeap, Function.update_of_ne (hslotNe 9 10 (by decide) (by decide) (by decide)), Function.update_self]
    have hbodyFlag : body.heap (BitVec.ofNat bits (header + 10)) =
        wordMask testBit (state.heap (BitVec.ofNat bits (header + 10))) := by
      rw [hbodyHeap, Function.update_self]
    have hbodyFrame : ∀ physical < header + 8, body.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
      intro physical hx
      rw [hbodyHeap, update_leading_frame _ header 10 _ hroom (by decide) (by decide) physical hx]
      exact update_leading_frame _ header 9 _ hroom (by decide) (by decide) physical hx
    have hbodyHigh : HighFrame (PSTRQueryLayout.endpoint workspace (treeSize q full) q) state.heap body.heap := by
      rw [hbodyHeap]
      exact (update_high_frame _ (header + 9) state.heap _ hend
        (scratch_lt_endpoint workspace (treeSize q full) q 9 (by decide))).trans
        (update_high_frame _ (header + 10) _ _ hend
          (scratch_lt_endpoint workspace (treeSize q full) q 10 (by decide)))
    have hrepBody := represents_of_leading_frame full configuration capWords state.heap body.heap
      (by omega) hq rep bitmap hs hroom hbodyFrame
    have hcache (offset : Nat) (ho : offset ≤ 13) : workspace + offset < header + 8 := by
      unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      omega
    have hwidthBody := (hbodyFrame _ (hcache 12 (by decide))).trans hwidth
    have hmaskBody := (hbodyFrame _ (hcache 13 (by decide))).trans hmask
    have heBody := (hslot 13 (by decide) (by decide) (by decide)).trans he
    have hfitBody : Fits bits remaining := (show remaining ≤ remaining + 1 by omega).trans_lt hrfit
    by_cases htest : count ≤ 5
    · rw [actual_nodeTest_prefix em rom state hp ha count htest]
      apply congrFun (executeOps_prefix_noStore rom (counterTest 9 (5 * (origin + 196))) state ?_ count) address
      simp [counterTest, counterLead, loadSlot, HeapPreservingOp]
    · have hfront : packingRun rom containing count state = packingRun rom containing (count - 5) test := by
        conv_lhs => rw [show count = 5 + (count - 5) by omega]
        exact run_add rom containing 5 (count - 5) state
      rw [hfront]
      by_cases hbody : count - 5 ≤ 93
      · have hpref : (packingRun rom containing (count - 5) test).heap address = test.heap address := by
          rw [actual_node_prefix em rom test htpc ht.2.2.2.2 (count - 5) hbody, nodeBody_as_kernel]
          apply executeOps_prefix_frame_append rom nodeKernel (back (5 * (origin + 98))) test address
          · intro cut hcut'
            exact nodeKernel_prefix_frame full command configuration capWords heapWords entryBase remaining test
              hb hq hw (by rw [htheap]; exact rep) bitmap hs hf halloc
              (by rw [htheap]; exact hwidth) (by rw [htheap]; exact hmask) ht.2.1 ht.1
              (by rw [htheap]; exact he) (by omega) (by omega) address h9 h10 cut
              (by simpa only [nodeKernel_length] using hcut')
          · intro cut _
            apply congrFun (executeOps_prefix_noStore _ _ _ ?_ cut) address
            simp [back, backLead, HeapPreservingOp]
          · simpa only [← nodeBody_as_kernel, nodeBody_length] using hbody
        exact hpref.trans (congrFun htheap address)
      · have htail : packingRun rom containing (count - 5) test =
            packingRun rom containing (count - 5 - 93) body := by
          conv_lhs => rw [show count - 5 = 93 + (count - 5 - 93) by omega]
          exact run_add rom containing 93 (count - 5 - 93) test
        rw [htail]
        have hi : (packingRun rom containing (count - 5 - 93) body).heap address = body.heap address := by
          apply ih body hrepBody hwidthBody hmaskBody hbodyAddress
            hbdy.2.2.1 hbdy.2.2.2 hbodyCounter heBody (by omega) (count - 5 - 93)
          unfold nodeClock at hcut ⊢
          omega
        have hb' : body.heap address = state.heap address := by
          rw [hbodyHeap, Function.update_of_ne h10, Function.update_of_ne h9]
        exact hi.trans hb'

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
