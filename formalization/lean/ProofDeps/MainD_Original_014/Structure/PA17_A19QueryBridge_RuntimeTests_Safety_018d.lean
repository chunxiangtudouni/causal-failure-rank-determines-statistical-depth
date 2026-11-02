module
public import Structure.PA17_A19QueryBridge_RuntimeTests_Safety_018c

/-! Every clock of the actual reverse node loop. Readiness for the recursive
iteration follows from its real two stores and genuine back jump. -/
@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeTests010

theorem core_after_leading {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords oldPC newPC : Nat) (before after : WordState bits)
    (ready : BudgetCoreReady full configuration capWords oldPC before)
    (hb : 0 < bits) (hq : 0 < q)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16))
    (frame : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 8, after.heap (BitVec.ofNat bits physical) = before.heap (BitVec.ofNat bits physical))
    (hh : after.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hp : after.pc = BitVec.ofNat bits (5 * newPC)) (ha : after.halted = false) :
    BudgetCoreReady full configuration capWords newPC after := by
  have hcache (offset : Nat) (ho : offset ≤ 13) :
      PSTRQueryLayout.physicalWorkspace full capWords bits + offset <
        PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8 := by
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  exact ⟨represents_of_leading_frame full configuration capWords before.heap after.heap hb hq
      ready.rep bitmap hs hroom frame,
    (frame _ (hcache 12 (by decide))).trans ready.width,
    (frame _ (hcache 13 (by decide))).trans ready.mask, hh, hp, ha⟩

theorem actual_nodeLoop_safe {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase remaining : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16 < heapWords)
    (ready : BudgetCoreReady full configuration capWords (origin + 98) state)
    (hc : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 9)) =
      BitVec.ofNat bits remaining)
    (he : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
      BitVec.ofNat bits entryBase)
    (hr : remaining ≤ treeSize q full) (hrow : entryBase + (treeSize q full + 1) ≤ capWords)
    (count : Nat) (hcut : count < nodeClock remaining) :
    StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing count state) := by
  let rom := callInput q full command
  let header := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have hslots : header + 9 < heapWords := by omega
  induction remaining generalizing state count with
  | zero =>
    exact nodeTest_safe em rom header heapWords state ready.header ready.pc_eq ready.active hslots count hcut
  | succ remaining ih =>
    have hrfit : Fits bits (remaining + 1) := (show remaining + 1 ≤ header by
      unfold header PSTRQueryLayout.header; omega).trans_lt hheader
    let test := packingRun rom containing 5 state
    let body := packingRun rom containing 93 test
    have ht := actual_nodeTest em rom header (remaining + 1) state ready.pc_eq ready.active ready.header hc hrfit
    have htpc : test.pc = BitVec.ofNat bits (5 * (origin + 103)) := by
      simpa only [show remaining + 1 ≠ 0 by omega, ite_false] using ht.2.2.2.1
    have htheap : test.heap = state.heap := ht.2.2.1
    have testReady : BudgetCoreReady full configuration capWords (origin + 103) test :=
      ⟨by rw [htheap]; exact ready.rep, by rw [htheap]; exact ready.width,
        by rw [htheap]; exact ready.mask, ht.2.1, htpc, ht.2.2.2.2⟩
    have hk := nodeKernel_result full command configuration capWords heapWords entryBase remaining test hb hq hw
      testReady.rep bitmap hs hf halloc testReady.width testReady.mask testReady.header ht.1
      (by rw [htheap]; exact he) (by omega) (by omega)
    have hbdy := actual_nodeBody_end em rom test htpc ht.2.2.2.2
    have hne (left right : Nat) (hl : left ≤ 16) (hr' : right ≤ 16) (hne : left ≠ right) :
        BitVec.ofNat bits (header + left) ≠ BitVec.ofNat bits (header + right) := by
      intro heq
      exact hne ((slots_eq_iff header left right hroom hl hr').mp heq)
    have hbodyCounter : body.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits remaining := by
      rw [hbdy.1, hk.1, Function.update_of_ne (hne 9 10 (by decide) (by decide) (by decide)), Function.update_self]
    have hbodyRow : body.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits entryBase := by
      rw [hbdy.1, hk.1, Function.update_of_ne (hne 13 10 (by decide) (by decide) (by decide)),
        Function.update_of_ne (hne 13 9 (by decide) (by decide) (by decide)), htheap]
      exact he
    have hbodyFrame : ∀ physical < header + 8,
        body.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
      intro physical hx
      rw [hbdy.1, hk.1, update_leading_frame _ header 10 _ hroom (by decide) (by decide) physical hx,
        update_leading_frame _ header 9 _ hroom (by decide) (by decide) physical hx, htheap]
    have bodyReady := core_after_leading full configuration capWords _ _ state body ready
      (by omega) hq bitmap hs hroom hbodyFrame (hbdy.2.1.trans hk.2) hbdy.2.2.1 hbdy.2.2.2
    by_cases htest : count < 5
    · exact nodeTest_safe em rom header heapWords state ready.header ready.pc_eq ready.active hslots count htest
    · have hfront : packingRun rom containing count state = packingRun rom containing (count - 5) test := by
        conv_lhs => rw [show count = 5 + (count - 5) by omega]
        exact run_add rom containing 5 (count - 5) state
      rw [hfront]
      by_cases hbody : count - 5 < 93
      · exact nodeBody_safe em full command configuration capWords heapWords entryBase remaining test hb hq hw
          bitmap hs hf halloc testReady ht.1 (by rw [htheap]; exact he) (by omega) (by omega) (count - 5) hbody
      · have htail : packingRun rom containing (count - 5) test =
            packingRun rom containing (count - 5 - 93) body := by
          conv_lhs => rw [show count - 5 = 93 + (count - 5 - 93) by omega]
          exact run_add rom containing 93 (count - 5 - 93) test
        rw [htail]
        apply ih body bodyReady hbodyCounter hbodyRow (by omega) (count - 5 - 93)
        unfold nodeClock at hcut ⊢
        omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
