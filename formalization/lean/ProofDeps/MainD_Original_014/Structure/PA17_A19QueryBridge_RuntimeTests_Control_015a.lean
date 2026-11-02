module

public import Structure.PA17_A19QueryBridge_RuntimeTests_010k
public import Structure.PA17_A19QueryBridge_RuntimeTests_010l
public import Structure.PA17_A19QueryBridge_RuntimeTests_010i
public import Structure.PA17_A19QueryBridge_RuntimeTests_010o

/-! Actual ancestor-loop control. The only ghost heap is original logicalHeap;
parent bounds are internal materialized-data facts, not a transition oracle. -/

@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def beforeAncestorTest (origin : Nat) : List PackingOp :=
  beforeNode origin ++ nodeBody origin ++ acceptFinish

theorem beforeAncestorTest_length (origin : Nat) : (beforeAncestorTest origin).length = 222 := by
  simp only [beforeAncestorTest, List.length_append, beforeNode_length, nodeBody_length, acceptFinish_length]

theorem ancestorTest_partition (origin : Nat) : programAt origin = beforeAncestorTest origin ++
    counterTest 12 (5 * (origin + 339)) ++ (ancestorBody origin ++ budgetFooter origin) := by
  simpa only [beforeAncestor, beforeAncestorTest, List.append_assoc] using ancestor_partition origin

theorem actual_ancestorTest_prefix {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 222))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 5) :
    packingRun rom containing count state =
      executeOps rom ((counterTest 12 (5 * (origin + 339))).take count) state := by
  exact actual_branch_phase_prefix em rom (beforeAncestorTest origin)
    (counterLead 12 (5 * (origin + 339))) (ancestorBody origin ++ budgetFooter origin)
    (.jumpIfZero .total .old) (ancestorTest_partition origin) (counterLead_straight _ _) state
    (by simpa only [beforeAncestorTest_length] using hp) ha count
    (by simpa only [counterLead_length] using hc)

theorem actual_ancestorTest {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header remaining : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 222))) (ha : state.halted = false)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hr : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits remaining)
    (hf : Fits bits remaining) :
    let after := packingRun rom containing 5 state
    after.register .total = BitVec.ofNat bits remaining ∧ after.register .address = BitVec.ofNat bits header ∧
      after.heap = state.heap ∧
      after.pc = BitVec.ofNat bits (5 * (origin + if remaining = 0 then 339 else 227)) ∧
      after.halted = false := by
  have hrun := actual_ancestorTest_prefix em rom state hp ha 5 (by decide)
  rw [List.take_of_length_le (by rw [counterTest_length])] at hrun
  have ht := execute_counterTest rom 12 (5 * (origin + 339)) header remaining state hh hr hf
  dsimp only
  rw [hrun]
  refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_, (executeOps_halted _ _ _).trans ha⟩
  rw [ht.2.2.2]
  by_cases hz : remaining = 0
  · simp only [hz, ite_true]
  · simp only [hz, ite_false, hp, BitVec.ofNat_add_ofNat]
    congr 1

theorem ancestorBody_as_kernel (origin : Nat) :
    ancestorBody origin = ancestorKernel ++ back (5 * (origin + 222)) := by
  simp only [ancestorBody, ancestorBodyLead, ancestorKernel, back, List.append_assoc]

theorem actual_ancestorBody_end {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 227))) (ha : state.halted = false) :
    let after := packingRun rom containing 112 state
    after.heap = (executeOps rom ancestorKernel state).heap ∧
      after.register .address = (executeOps rom ancestorKernel state).register .address ∧
      after.pc = BitVec.ofNat bits (5 * (origin + 222)) ∧ after.halted = false := by
  have hrun := actual_ancestor_prefix em rom state hp ha 112 (by decide)
  rw [List.take_of_length_le (by rw [ancestorBody_length]), ancestorBody_as_kernel, executeOps_append] at hrun
  have hb := execute_back rom (5 * (origin + 222)) (executeOps rom ancestorKernel state)
  dsimp only
  rw [hrun]
  exact ⟨hb.2.1, hb.2.2, hb.1, (executeOps_halted _ _ _).trans ((executeOps_halted _ _ _).trans ha)⟩

theorem chainPrefix_congr (old fresh : Nat → Nat) (entryBase countsBase parentBase size fuel encoded : Nat)
    (hparents : ∀ e ≤ size, old (parentBase + e) ≤ size)
    (he : encoded ≤ size)
    (hc : ∀ node < size, fresh (countsBase + node) = old (countsBase + node))
    (hr : ∀ node < size, fresh (entryBase + 1 + node) = old (entryBase + 1 + node))
    (hp : ∀ e ≤ size, fresh (parentBase + e) = old (parentBase + e)) :
    chainPrefix fresh entryBase countsBase parentBase fuel encoded =
      chainPrefix old entryBase countsBase parentBase fuel encoded := by
  induction fuel generalizing encoded with
  | zero => rfl
  | succ fuel ih =>
    rw [chainPrefix, chainPrefix, hp encoded he, ih _ (hparents encoded he)]
    by_cases hz : encoded = 0
    · simp only [hz, ite_true]
    · rw [ite_eq_right hz, ite_eq_right hz, hc (encoded - 1) (by omega), hr (encoded - 1) (by omega)]

def ancestorClock (fuel : Nat) : Nat := 5 + 117 * fuel

structure AncestorLoopPost {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords entryBase fuel encoded origin : Nat) (before after : WordState bits) : Prop where
  active : after.halted = false
  pc : after.pc = BitVec.ofNat bits (5 * (origin + 339))
  header : after.register .address = BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
  counter : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 12)) =
    BitVec.ofNat bits 0
  flag : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 14)) =
    wordMask (chainPrefix (logicalHeap q capWords before.heap) entryBase
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)) fuel encoded)
      (before.heap (BitVec.ofNat bits
        (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 14)))
  «outside» : ∀ address,
    address ≠ BitVec.ofNat bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 11) →
    address ≠ BitVec.ofNat bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 12) →
    address ≠ BitVec.ofNat bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 14) → after.heap address = before.heap address
  leading : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 8, after.heap (BitVec.ofNat bits physical) = before.heap (BitVec.ofNat bits physical)
  high : HighFrame (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits)
    (treeSize q full) q) before.heap after.heap

theorem actual_ancestorLoop {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase fuel encoded : Nat)
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
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 222))) (ha : state.halted = false)
    (hc : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 12)) =
      BitVec.ofNat bits fuel)
    (he : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
      BitVec.ofNat bits entryBase)
    (hae : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 11)) =
      BitVec.ofNat bits encoded)
    (hr : fuel ≤ treeSize q full) (hn : encoded ≤ treeSize q full)
    (hrow : entryBase + (treeSize q full + 1) ≤ capWords)
    (hparents : ∀ e ≤ treeSize q full, logicalHeap q capWords state.heap
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full) :
    AncestorLoopPost full capWords entryBase fuel encoded origin state
      (packingRun (callInput q full command) containing (ancestorClock fuel) state) := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let logicalHeader := PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)
  let logicalCounts := PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)
  let logicalParents := PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  induction fuel generalizing state encoded with
  | zero =>
    have hrfit : Fits bits 0 := (show 0 ≤ header by omega).trans_lt hheader
    have ht := actual_ancestorTest em rom header 0 state hp ha hh hc hrfit
    change AncestorLoopPost full capWords entryBase 0 encoded origin state (packingRun rom containing 5 state)
    refine ⟨ht.2.2.2.2, ?_, ht.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [ite_true] using ht.2.2.2.1
    · rw [ht.2.2.1]; exact hc
    · rw [ht.2.2.1]; rfl
    · intro address _ _ _; rw [ht.2.2.1]
    · intro physical _; rw [ht.2.2.1]
    · intro physical _ _; rw [ht.2.2.1]
  | succ fuel ih =>
    have hrfit : Fits bits (fuel + 1) := (show fuel + 1 ≤ header by
      unfold header PSTRQueryLayout.header; omega).trans_lt hheader
    let test := packingRun rom containing 5 state
    let body := packingRun rom containing 112 test
    let next := logicalHeap q capWords state.heap (logicalParents + encoded)
    let testBit := if encoded = 0 then true else decide
      (logicalHeap q capWords state.heap (logicalCounts + (encoded - 1)) <
        logicalHeap q capWords state.heap (entryBase + 1 + (encoded - 1)))
    have ht := actual_ancestorTest em rom header (fuel + 1) state hp ha hh hc hrfit
    have htpc : test.pc = BitVec.ofNat bits (5 * (origin + 227)) := by
      simpa only [show fuel + 1 ≠ 0 by omega, ite_false] using ht.2.2.2.1
    have htheap : test.heap = state.heap := ht.2.2.1
    have hk := ancestorKernel_result full command configuration capWords heapWords entryBase fuel encoded test hb hq hw
      (by rw [htheap]; exact rep) bitmap hs hf halloc
      (by rw [htheap]; exact hwidth) (by rw [htheap]; exact hmask) ht.2.1 ht.1
      (by rw [htheap]; exact he) (by rw [htheap]; exact hae) (by omega) hn (by omega)
    have hbdy := actual_ancestorBody_end em rom test htpc ht.2.2.2.2
    have hbodyHeap : body.heap = Function.update
        (Function.update (Function.update state.heap
          (BitVec.ofNat bits (header + 12)) (BitVec.ofNat bits fuel))
          (BitVec.ofNat bits (header + 14)) (wordMask testBit (state.heap (BitVec.ofNat bits (header + 14)))))
          (BitVec.ofNat bits (header + 11)) (BitVec.ofNat bits next) := by
      rw [hbdy.1, hk.1, htheap, ← logical_counts_word full capWords (encoded - 1) state.heap hq]
      have hpword : BitVec.ofNat bits next = state.heap
          (BitVec.ofNat bits (PSTRQueryLayout.parentsBase workspace (treeSize q full) + encoded)) := by
        dsimp only [next, logicalParents]
        rw [logical_parent_word full capWords (treeSize q full) encoded state.heap hq]
        simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rfl
      rw [hpword]
      by_cases hz : encoded = 0
      · simp [testBit, wordMask, hz]
        rfl
      · simp [testBit, wordMask, hz, logicalCounts]
        rfl
    have hbodyAddress : body.register .address = BitVec.ofNat bits header := hbdy.2.1.trans hk.2
    have hslotNe (left right : Nat) (hl : left ≤ 16) (hr' : right ≤ 16) (hne : left ≠ right) :
        BitVec.ofNat bits (header + left) ≠ BitVec.ofNat bits (header + right) := by
      intro h
      exact hne ((slots_eq_iff header left right hroom hl hr').mp h)
    have hbodyOutside (address : BitVec bits) (h11 : address ≠ BitVec.ofNat bits (header + 11))
        (h12 : address ≠ BitVec.ofNat bits (header + 12)) (h14 : address ≠ BitVec.ofNat bits (header + 14)) :
        body.heap address = state.heap address := by
      rw [hbodyHeap, Function.update_of_ne h11, Function.update_of_ne h14, Function.update_of_ne h12]
    have hslot (offset : Nat) (ho : offset ≤ 16) (h11 : offset ≠ 11) (h12 : offset ≠ 12) (h14 : offset ≠ 14) :=
      hbodyOutside (BitVec.ofNat bits (header + offset))
        (hslotNe offset 11 ho (by decide) h11) (hslotNe offset 12 ho (by decide) h12)
        (hslotNe offset 14 ho (by decide) h14)
    have hbodyCounter : body.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits fuel := by
      rw [hbodyHeap, Function.update_of_ne (hslotNe 12 11 (by decide) (by decide) (by decide)),
        Function.update_of_ne (hslotNe 12 14 (by decide) (by decide) (by decide)), Function.update_self]
    have hbodyEncoded : body.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits next := by
      rw [hbodyHeap, Function.update_self]
    have hbodyFlag : body.heap (BitVec.ofNat bits (header + 14)) =
        wordMask testBit (state.heap (BitVec.ofNat bits (header + 14))) := by
      rw [hbodyHeap, Function.update_of_ne (hslotNe 14 11 (by decide) (by decide) (by decide)), Function.update_self]
    have hbodyFrame : ∀ physical < header + 8, body.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
      intro physical hx
      rw [hbodyHeap, update_leading_frame _ header 11 _ hroom (by decide) (by decide) physical hx,
        update_leading_frame _ header 14 _ hroom (by decide) (by decide) physical hx]
      exact update_leading_frame _ header 12 _ hroom (by decide) (by decide) physical hx
    have hbodyHigh : HighFrame (PSTRQueryLayout.endpoint workspace (treeSize q full) q) state.heap body.heap := by
      rw [hbodyHeap]
      exact ((update_high_frame _ (header + 12) state.heap _ hend
        (scratch_lt_endpoint workspace (treeSize q full) q 12 (by decide))).trans
        (update_high_frame _ (header + 14) _ _ hend
          (scratch_lt_endpoint workspace (treeSize q full) q 14 (by decide)))).trans
        (update_high_frame _ (header + 11) _ _ hend
          (scratch_lt_endpoint workspace (treeSize q full) q 11 (by decide)))
    have hrepBody := represents_of_leading_frame full configuration capWords state.heap body.heap
      (by omega) hq rep bitmap hs hroom hbodyFrame
    have hcache (offset : Nat) (ho : offset ≤ 13) : workspace + offset < header + 8 := by
      unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      omega
    have hwidthBody := (hbodyFrame _ (hcache 12 (by decide))).trans hwidth
    have hmaskBody := (hbodyFrame _ (hcache 13 (by decide))).trans hmask
    have heBody := (hslot 13 (by decide) (by decide) (by decide) (by decide)).trans he
    have hlogicalFrame := logical_leading_frame full capWords (treeSize q full) state.heap body.heap
      (by omega) hq hs hroom hbodyFrame
    have hparentsFrame (e : Nat) (hle : e ≤ treeSize q full) :
        logicalHeap q capWords body.heap (logicalParents + e) =
          logicalHeap q capWords state.heap (logicalParents + e) := by
      apply hlogicalFrame
      unfold logicalParents PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      omega
    have hparentsBody : ∀ e ≤ treeSize q full, logicalHeap q capWords body.heap (logicalParents + e) ≤ treeSize q full := by
      intro e hle
      rw [hparentsFrame e hle]
      exact hparents e hle
    have hnext : next ≤ treeSize q full := hparents encoded hn
    have hi : AncestorLoopPost full capWords entryBase fuel next origin body
        (packingRun rom containing (ancestorClock fuel) body) := by
      apply ih next body hrepBody hwidthBody hmaskBody hbodyAddress hbdy.2.2.1 hbdy.2.2.2
        hbodyCounter heBody hbodyEncoded (by omega) hnext hparentsBody
    have hpref : chainPrefix (logicalHeap q capWords body.heap) entryBase logicalCounts logicalParents fuel next =
        chainPrefix (logicalHeap q capWords state.heap) entryBase logicalCounts logicalParents fuel next := by
      apply chainPrefix_congr _ _ _ _ _ (treeSize q full) _ _ hparents hnext
      · intro node hn'
        apply hlogicalFrame
        unfold logicalCounts PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
        omega
      · intro node hn'
        apply hlogicalFrame
        unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
          PSTRQueryLayout.logicalWorkspace
        omega
      · exact hparentsFrame
    have hclock : ancestorClock (fuel + 1) = 5 + (112 + ancestorClock fuel) := by unfold ancestorClock; omega
    have hrun : packingRun rom containing (ancestorClock (fuel + 1)) state =
        packingRun rom containing (ancestorClock fuel) body := by
      rw [hclock, run_add, run_add]
    rw [hrun]
    refine ⟨hi.active, hi.pc, hi.header, hi.counter, ?_, ?_, ?_, hbodyHigh.trans hi.high⟩
    · rw [hi.flag, hpref, hbodyFlag, wordMask_and]
      rfl
    · intro address h11 h12 h14
      exact (hi.«outside» address h11 h12 h14).trans (hbodyOutside address h11 h12 h14)
    · intro physical hx
      exact (hi.leading physical hx).trans (hbodyFrame physical hx)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
