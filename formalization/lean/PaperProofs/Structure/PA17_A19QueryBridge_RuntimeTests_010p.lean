module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010i
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010o

/-! Actual reverse-node loop induction, with a concrete clock and one logical
ghost heap. This component concerns the node loop; outer budget/ancestor loops
and every-clock access/frame certificates are separate obligations. -/

@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def nodeClock (remaining : Nat) : Nat := 5 + 98 * remaining

structure NodeLoopPost {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords entryBase remaining origin : Nat) (before after : WordState bits) : Prop where
  active : after.halted = false
  pc : after.pc = BitVec.ofNat bits (5 * (origin + 196))
  header : after.register .address = BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
  counter : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 9)) =
    BitVec.ofNat bits 0
  flag : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 10)) =
    wordMask (acceptPrefix (logicalHeap q capWords before.heap) entryBase
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)) remaining)
      (before.heap (BitVec.ofNat bits
        (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 10)))
  budget : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8)) =
    before.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8))
  entry : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
    before.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13))
  leading : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 8, after.heap (BitVec.ofNat bits physical) = before.heap (BitVec.ofNat bits physical)
  high : HighFrame (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits)
    (treeSize q full) q) before.heap after.heap
  «outside» : ∀ address : BitVec bits,
    address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 9) →
    address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 10) →
    after.heap address = before.heap address

theorem actual_nodeLoop {bits q origin : Nat} {containing : List PackingOp}
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
    (hr : remaining ≤ treeSize q full) (hrow : entryBase + (treeSize q full + 1) ≤ capWords) :
    NodeLoopPost full capWords entryBase remaining origin state
      (packingRun (callInput q full command) containing (nodeClock remaining) state) := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let logicalHeader := PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)
  let logicalCounts := PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  induction remaining generalizing state with
  | zero =>
    have hrfit : Fits bits 0 := (show 0 ≤ header by omega).trans_lt hheader
    have ht := actual_nodeTest em rom header 0 state hp ha hh hc hrfit
    change NodeLoopPost full capWords entryBase 0 origin state (packingRun rom containing 5 state)
    refine ⟨ht.2.2.2.2, ?_, ht.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [ite_true] using ht.2.2.2.1
    · rw [ht.2.2.1]; exact hc
    · rw [ht.2.2.1]; rfl
    · rw [ht.2.2.1]
    · rw [ht.2.2.1]
    · intro physical _; rw [ht.2.2.1]
    · intro physical _ _; rw [ht.2.2.1]
    · intro address _ _; rw [ht.2.2.1]
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
    have hi : NodeLoopPost full capWords entryBase remaining origin body
        (packingRun rom containing (nodeClock remaining) body) := by
      apply ih body hrepBody hwidthBody hmaskBody hbodyAddress hbdy.2.2.1 hbdy.2.2.2 hbodyCounter heBody
      all_goals omega
    have hlogicalFrame := logical_leading_frame full capWords (treeSize q full) state.heap body.heap
      (by omega) hq hs hroom hbodyFrame
    have hpref : acceptPrefix (logicalHeap q capWords body.heap) entryBase logicalCounts remaining =
        acceptPrefix (logicalHeap q capWords state.heap) entryBase logicalCounts remaining := by
      apply acceptPrefix_congr
      intro node hn
      constructor
      · apply hlogicalFrame
        unfold logicalCounts PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
        omega
      · apply hlogicalFrame
        unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
          PSTRQueryLayout.logicalWorkspace
        omega
    have hclock : nodeClock (remaining + 1) = 5 + (93 + nodeClock remaining) := by unfold nodeClock; omega
    have hrun : packingRun rom containing (nodeClock (remaining + 1)) state =
        packingRun rom containing (nodeClock remaining) body := by
      rw [hclock, run_add, run_add]
    rw [hrun]
    refine ⟨hi.active, hi.pc, hi.header, hi.counter, ?_, ?_, ?_, ?_, hbodyHigh.trans hi.high, ?_⟩
    · rw [hi.flag, hpref, hbodyFlag, wordMask_and]
      simp only [testBit, acceptPrefix_succ, header, workspace, logicalCounts]
    · exact hi.budget.trans (hslot 8 (by decide) (by decide) (by decide))
    · exact hi.entry.trans (hslot 13 (by decide) (by decide) (by decide))
    · intro physical hx
      exact (hi.leading physical hx).trans (hbodyFrame physical hx)
    · intro address h9 h10
      have hb' : body.heap address = state.heap address := by
        rw [hbodyHeap, Function.update_of_ne h10, Function.update_of_ne h9]
      exact (hi.«outside» address h9 h10).trans hb'

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
