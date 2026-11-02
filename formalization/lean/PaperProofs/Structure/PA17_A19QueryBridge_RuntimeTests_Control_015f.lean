module
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015e

/-! Every actual ancestor-loop clock preserves every cell outside its three
scratch slots, including HD's complete high region. No prefix frame oracle. -/
@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem actual_ancestorLoop_prefix_frame {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase fuel encoded : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16 < heapWords)

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
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full)
    (address : BitVec bits)
    (h11 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 11))
    (h12 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 12))
    (h14 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 14))
    (count : Nat) (hcut : count ≤ ancestorClock fuel) :
    (packingRun (callInput q full command) containing count state).heap address = state.heap address := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let logicalHeader := PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)
  let logicalCounts := PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)
  let logicalParents := PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  induction fuel generalizing state encoded count with
  | zero =>
    have htest : count ≤ 5 := hcut
    rw [actual_ancestorTest_prefix em rom state hp ha count htest]
    apply congrFun (executeOps_prefix_noStore rom (counterTest 12 (5 * (origin + 339))) state ?_ count) address
    simp [counterTest, counterLead, loadSlot, HeapPreservingOp]
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
    by_cases htest : count ≤ 5
    · rw [actual_ancestorTest_prefix em rom state hp ha count htest]
      apply congrFun (executeOps_prefix_noStore rom (counterTest 12 (5 * (origin + 339))) state ?_ count) address
      simp [counterTest, counterLead, loadSlot, HeapPreservingOp]
    · have hfront : packingRun rom containing count state = packingRun rom containing (count - 5) test := by
        conv_lhs => rw [show count = 5 + (count - 5) by omega]
        exact run_add rom containing 5 (count - 5) state
      rw [hfront]
      by_cases hbody : count - 5 ≤ 112
      · have hpref := actual_ancestorBody_prefix_frame em full command configuration capWords heapWords entryBase fuel encoded test
          hb hq hw (by rw [htheap]; exact rep) bitmap hs hf halloc
          (by rw [htheap]; exact hwidth) (by rw [htheap]; exact hmask) ht.2.1 htpc ht.2.2.2.2 ht.1
          (by rw [htheap]; exact he) (by rw [htheap]; exact hae) (by omega) hn (by omega)
          address h11 h12 h14 (count - 5) hbody
        exact hpref.trans (congrFun htheap address)
      · have htail : packingRun rom containing (count - 5) test =
            packingRun rom containing (count - 5 - 112) body := by
          conv_lhs => rw [show count - 5 = 112 + (count - 5 - 112) by omega]
          exact run_add rom containing 112 (count - 5 - 112) test
        rw [htail]
        have hi : (packingRun rom containing (count - 5 - 112) body).heap address = body.heap address := by
          apply ih next body hrepBody hwidthBody hmaskBody hbodyAddress
            hbdy.2.2.1 hbdy.2.2.2 hbodyCounter heBody hbodyEncoded (by omega) hnext hparentsBody (count - 5 - 112)
          unfold ancestorClock at hcut ⊢
          omega
        exact hi.trans (hbodyOutside address h11 h12 h14)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
