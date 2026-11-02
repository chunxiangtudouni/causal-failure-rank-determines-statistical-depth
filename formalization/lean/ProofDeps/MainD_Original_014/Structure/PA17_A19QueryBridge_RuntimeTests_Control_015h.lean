module

public import Structure.PA17_A19QueryBridge_RuntimeTests_Control_015g
public import Structure.PA17_A19QueryBridge_RuntimeTests_010q

/-! Actual outer budget-loop induction. The body is the proved concrete
actual_budget_block; there is no caller-supplied transition/performance oracle. -/

@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def outerClock (size remaining : Nat) : Nat := 5 + remaining * (5 + budgetBlockClock size)

structure OuterLoopPost {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords rowBase remaining encoded origin : Nat) (before after : WordState bits) : Prop where
  active : after.halted = false
  pc : after.pc = BitVec.ofNat bits (5 * (origin + 355))
  header : after.register .address = BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
  counter : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8)) = BitVec.ofNat bits 0
  good : ∀ budget < remaining, after.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 + budget)) =
    BitVec.ofNat bits (bit (rawGood (logicalHeap q capWords before.heap)
      (rowBase + budget * (treeSize q full + 1))
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)) (treeSize q full)))
  bad : ∀ budget < remaining, after.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 + (q + 2) + budget)) =
    BitVec.ofNat bits (bit (rawBad (logicalHeap q capWords before.heap)
      (rowBase + budget * (treeSize q full + 1))
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)) (treeSize q full) encoded))
  «outside» : ∀ address,
    (∀ offset, 8 ≤ offset → offset ≤ 14 → address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + offset)) →
    (∀ budget < remaining,
      address ≠ BitVec.ofNat bits
        (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 + budget) ∧
      address ≠ BitVec.ofNat bits
        (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 + (q + 2) + budget)) →
      after.heap address = before.heap address
  leading : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 8, after.heap (BitVec.ofNat bits physical) = before.heap (BitVec.ofNat bits physical)
  high : HighFrame (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits)
    (treeSize q full) q) before.heap after.heap

theorem actual_budgetLoop {bits q origin : Nat} {containing : List PackingOp}
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
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full) :
    OuterLoopPost full capWords rowBase remaining encoded origin state
      (packingRun (callInput q full command) containing (outerClock (treeSize q full) remaining) state) := by
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
  induction remaining generalizing state with
  | zero =>
    have ht := actual_budgetTest em rom header 0 state hp ha hh hcounter
      ((show 0 ≤ q + 2 by omega).trans_lt hqfit)
    simp only [outerClock, Nat.zero_mul, Nat.add_zero]
    change OuterLoopPost full capWords rowBase 0 encoded origin state (packingRun rom containing 5 state)
    refine ⟨ht.2.2.2.2, ?_, ht.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [ite_true] using ht.2.2.2.1
    · rw [ht.2.2.1]; exact hcounter
    · intro budget hbudget; omega
    · intro budget hbudget; omega
    · intro address _ _; rw [ht.2.2.1]
    · intro physical _; rw [ht.2.2.1]
    · intro physical _ _; rw [ht.2.2.1]
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
    have hi : OuterLoopPost full capWords rowBase remaining encoded origin body
        (packingRun rom containing (outerClock (treeSize q full) remaining) body) := by
      apply ih body hrepBody hwidthBody hmaskBody block.header block.pc block.active block.counter
        hrowBody hnodeBody (by omega) hparentsBody
    have hgood (budget : Nat) (hbudget : budget < remaining) :
        rawGood (logicalHeap q capWords body.heap) (rowBase + budget * (treeSize q full + 1))
          (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)) (treeSize q full) =
        rawGood (logicalHeap q capWords state.heap) (rowBase + budget * (treeSize q full + 1))
          (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)) (treeSize q full) := by
      apply rawGood_of_leading_frame full capWords _ state.heap body.heap (by omega) hq hs hroom hbodyFrame
      have hm := Nat.mul_le_mul_right (treeSize q full + 1) (show budget + 1 ≤ q + 2 by omega)
      nlinarith
    have hbad (budget : Nat) (hbudget : budget < remaining) :=
      rawBad_of_leading_frame full capWords (rowBase + budget * (treeSize q full + 1)) encoded
        state.heap body.heap (by omega) hq hs hroom hbodyFrame
        (by have hm := Nat.mul_le_mul_right (treeSize q full + 1) (show budget + 1 ≤ q + 2 by omega); nlinarith)
        hencoded hparents
    have hcurrent (address : BitVec bits)
        (hscratch : ∀ offset, 8 ≤ offset → offset ≤ 14 → address ≠ BitVec.ofNat bits (header + offset))
        (hflags : ∀ budget < remaining, address ≠ BitVec.ofNat bits (header + 16 + budget) ∧
          address ≠ BitVec.ofNat bits (header + 16 + (q + 2) + budget)) :
        (packingRun rom containing (outerClock (treeSize q full) remaining) body).heap address = body.heap address :=
      hi.«outside» address hscratch hflags
    have hkeepCurrent (bad : Bool) :
        (packingRun rom containing (outerClock (treeSize q full) remaining) body).heap
            (BitVec.ofNat bits (header + 16 + (if bad then q + 2 else 0) + remaining)) =
          body.heap (BitVec.ofNat bits (header + 16 + (if bad then q + 2 else 0) + remaining)) := by
      apply hcurrent
      · intro offset hlo hhi
        apply wordNe
        · cases bad <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
          · exact good_lt_endpoint workspace (treeSize q full) q remaining (by omega)
          · exact bad_lt_endpoint workspace (treeSize q full) q remaining (by omega)
        · exact scratch_lt_endpoint workspace (treeSize q full) q offset (by omega)
        · cases bad <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
      · intro budget hbudget
        constructor
        · apply wordNe
          · cases bad <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
            · exact good_lt_endpoint workspace (treeSize q full) q remaining (by omega)
            · exact bad_lt_endpoint workspace (treeSize q full) q remaining (by omega)
          · exact good_lt_endpoint workspace (treeSize q full) q budget (by omega)
          · cases bad <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
        · apply wordNe
          · cases bad <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
            · exact good_lt_endpoint workspace (treeSize q full) q remaining (by omega)
            · exact bad_lt_endpoint workspace (treeSize q full) q remaining (by omega)
          · exact bad_lt_endpoint workspace (treeSize q full) q budget (by omega)
          · cases bad <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
    have hclock : outerClock (treeSize q full) (remaining + 1) =
        5 + (budgetBlockClock (treeSize q full) + outerClock (treeSize q full) remaining) := by
      simp only [outerClock, Nat.add_mul, Nat.one_mul]
      omega
    have hrun : packingRun rom containing (outerClock (treeSize q full) (remaining + 1)) state =
        packingRun rom containing (outerClock (treeSize q full) remaining) body := by
      rw [hclock, run_add, run_add]
    rw [hrun]
    refine ⟨hi.active, hi.pc, hi.header, hi.counter, ?_, ?_, ?_, ?_, hbodyHigh.trans hi.high⟩
    · intro budget hbudget
      by_cases heq : budget = remaining
      · subst budget
        have hk := hkeepCurrent false
        simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hk
        rw [hk, block.good, htheap]
      · rw [hi.good budget (by omega), hgood budget (by omega)]
    · intro budget hbudget
      by_cases heq : budget = remaining
      · subst budget
        have hk := hkeepCurrent true
        simp only [ite_true] at hk
        rw [hk, block.bad, htheap]
      · rw [hi.bad budget (by omega), hbad budget (by omega)]
    · intro address hscratch hflags
      exact (hi.«outside» address hscratch (fun budget hbudget => hflags budget (by omega))).trans
        ((block.«outside» address hscratch (hflags remaining (by omega)).1 (hflags remaining (by omega)).2).trans
          (congrFun htheap address))
    · intro physical hphysical
      exact (hi.leading physical hphysical).trans (hbodyFrame physical hphysical)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
