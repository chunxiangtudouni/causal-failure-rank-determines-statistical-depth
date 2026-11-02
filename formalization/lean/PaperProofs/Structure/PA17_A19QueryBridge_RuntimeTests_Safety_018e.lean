module
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Safety_018d

/-! Every clock of the actual t-fuel ancestor loop. Each successor node is
read from the represented parent array of this same physical heap. -/
@[expose] public section
set_option maxRecDepth 28000
set_option maxHeartbeats 2800000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeTests010

theorem actual_ancestorLoop_safe {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase fuel encoded : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16 < heapWords)
    (ready : BudgetCoreReady full configuration capWords (origin + 222) state)
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
    (count : Nat) (hcut : count < ancestorClock fuel) :
    StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing count state) := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let logicalParents := PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have hslots : header + 12 < heapWords := by
    change header + 16 < heapWords at halloc
    omega
  induction fuel generalizing state encoded count with
  | zero =>
    exact ancestorTest_safe em rom header heapWords state ready.header ready.pc_eq ready.active hslots count hcut
  | succ fuel ih =>
    have hrfit : Fits bits (fuel + 1) := (show fuel + 1 ≤ header by
      unfold header PSTRQueryLayout.header; omega).trans_lt hheader
    let test := packingRun rom containing 5 state
    let body := packingRun rom containing 112 test
    let next := logicalHeap q capWords state.heap (logicalParents + encoded)
    have ht := actual_ancestorTest em rom header (fuel + 1) state ready.pc_eq ready.active ready.header hc hrfit
    have htpc : test.pc = BitVec.ofNat bits (5 * (origin + 227)) := by
      simpa only [show fuel + 1 ≠ 0 by omega, ite_false] using ht.2.2.2.1
    have htheap : test.heap = state.heap := ht.2.2.1
    have testReady : BudgetCoreReady full configuration capWords (origin + 227) test :=
      ⟨by rw [htheap]; exact ready.rep, by rw [htheap]; exact ready.width,
        by rw [htheap]; exact ready.mask, ht.2.1, htpc, ht.2.2.2.2⟩
    have hk := ancestorKernel_result full command configuration capWords heapWords entryBase fuel encoded test hb hq hw
      testReady.rep bitmap hs hf halloc testReady.width testReady.mask testReady.header ht.1
      (by rw [htheap]; exact he) (by rw [htheap]; exact hae) (by omega) hn (by omega)
    have hbdy := actual_ancestorBody_end em rom test htpc ht.2.2.2.2
    have hne (left right : Nat) (hl : left ≤ 16) (hr' : right ≤ 16) (hne : left ≠ right) :
        BitVec.ofNat bits (header + left) ≠ BitVec.ofNat bits (header + right) := by
      intro heq
      exact hne ((slots_eq_iff header left right hroom hl hr').mp heq)
    have hbodyCounter : body.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits fuel := by
      rw [hbdy.1, hk.1, Function.update_of_ne (hne 12 11 (by decide) (by decide) (by decide)),
        Function.update_of_ne (hne 12 14 (by decide) (by decide) (by decide)), Function.update_self]
    have hbodyRow : body.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits entryBase := by
      rw [hbdy.1, hk.1, Function.update_of_ne (hne 13 11 (by decide) (by decide) (by decide)),
        Function.update_of_ne (hne 13 14 (by decide) (by decide) (by decide)),
        Function.update_of_ne (hne 13 12 (by decide) (by decide) (by decide)), htheap]
      exact he
    have hbodyEncoded : body.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits next := by
      rw [hbdy.1, hk.1, Function.update_self, htheap]
      dsimp only [next, logicalParents]
      rw [logical_parent_word full capWords (treeSize q full) encoded state.heap hq]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hbodyFrame : ∀ physical < header + 8,
        body.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
      intro physical hx
      rw [hbdy.1, hk.1, update_leading_frame _ header 11 _ hroom (by decide) (by decide) physical hx,
        update_leading_frame _ header 14 _ hroom (by decide) (by decide) physical hx,
        update_leading_frame _ header 12 _ hroom (by decide) (by decide) physical hx, htheap]
    have bodyReady := core_after_leading full configuration capWords _ _ state body ready
      (by omega) hq bitmap hs hroom hbodyFrame (hbdy.2.1.trans hk.2) hbdy.2.2.1 hbdy.2.2.2
    have hlogical := logical_leading_frame full capWords (treeSize q full) state.heap body.heap
      (by omega) hq hs hroom hbodyFrame
    have hparentsBody : ∀ e ≤ treeSize q full, logicalHeap q capWords body.heap (logicalParents + e) ≤ treeSize q full := by
      intro e hle
      rw [hlogical _ (by unfold logicalParents PSTRQueryLayout.header; omega)]
      exact hparents e hle
    have hnext : next ≤ treeSize q full := hparents encoded hn
    by_cases htest : count < 5
    · exact ancestorTest_safe em rom header heapWords state ready.header ready.pc_eq ready.active hslots count htest
    · have hfront : packingRun rom containing count state = packingRun rom containing (count - 5) test := by
        conv_lhs => rw [show count = 5 + (count - 5) by omega]
        exact run_add rom containing 5 (count - 5) state
      rw [hfront]
      by_cases hbody : count - 5 < 112
      · exact ancestorBody_safe em full command configuration capWords heapWords entryBase fuel encoded test hb hq hw
          bitmap hs hf halloc testReady ht.1 (by rw [htheap]; exact he) (by rw [htheap]; exact hae)
          (by omega) hn (by omega) (count - 5) hbody
      · have htail : packingRun rom containing (count - 5) test =
            packingRun rom containing (count - 5 - 112) body := by
          conv_lhs => rw [show count - 5 = 112 + (count - 5 - 112) by omega]
          exact run_add rom containing 112 (count - 5 - 112) test
        rw [htail]
        apply ih next body bodyReady hbodyCounter hbodyRow hbodyEncoded (by omega) hnext hparentsBody (count - 5 - 112)
        unfold ancestorClock at hcut ⊢
        omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
