module
public import Structure.PA17_A19QueryBridge_RuntimeTests_Control_015h

/-! Actual setup and all outer budgets, from same-call materialized header.
Incoming H8..H15 and other scratch registers are arbitrary. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem actual_tests_from_materialized_header {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords rowBase encoded : Nat)
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
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (hrowPointer : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))) =
      BitVec.ofNat bits rowBase)
    (hnodePointer : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 1)) =
      BitVec.ofNat bits encoded)
    (hencoded : encoded ≤ treeSize q full)
    (hrowExtent : rowBase + (q + 2) * (treeSize q full + 1) ≤ capWords)
    (hparents : ∀ e ≤ treeSize q full, logicalHeap q capWords state.heap
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full) :
    OuterLoopPost full capWords rowBase (q + 2) encoded origin state
      (packingRun (callInput q full command) containing (steps q (treeSize q full)) state) := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let endpoint := PSTRQueryLayout.endpoint workspace (treeSize q full) q
  let initialized := packingRun rom containing 7 state
  have hend : Fits bits endpoint := hendpoint_alloc.trans_lt hf
  have hroom : Fits bits (header + 16) := (show header + 16 < endpoint by
    unfold endpoint PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega).trans hend
  have hqfit : Fits bits (q + 2) := (show q + 2 ≤ endpoint by
    unfold endpoint PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega).trans_lt hend
  have hromq : (rom.words .input).getD 1 0 = q := by
    rfl
  have setup := actual_setup em rom header q state hp ha hh hromq hqfit
  have hframe : ∀ physical < header + 8, initialized.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    intro physical hphysical
    rw [setup.1]
    exact update_leading_frame state.heap header 8 _ hroom (by decide) (by decide) physical hphysical
  have hrep := represents_of_leading_frame full configuration capWords state.heap initialized.heap
    (by omega) hq rep bitmap hs hroom hframe
  have hcache (offset : Nat) (ho : offset ≤ 13) : workspace + offset < header + 8 := by
    unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have hwidth' := (hframe _ (hcache 12 (by decide))).trans hwidth
  have hmask' := (hframe _ (hcache 13 (by decide))).trans hmask
  have hrow' := (hframe header (by omega)).trans hrowPointer
  have hnode' := (hframe (header + 1) (by omega)).trans hnodePointer
  have hcounter : initialized.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (q + 2) := by
    rw [setup.1, Function.update_self]
  have hlogical := logical_leading_frame full capWords (treeSize q full) state.heap initialized.heap
    (by omega) hq hs hroom hframe
  have hparents' : ∀ e ≤ treeSize q full, logicalHeap q capWords initialized.heap
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full := by
    intro e he
    rw [hlogical _ (by unfold PSTRQueryLayout.header; omega)]
    exact hparents e he
  have loop := actual_budgetLoop em full command configuration capWords heapWords rowBase (q + 2) encoded initialized
    hb hq hw hrep bitmap hs hf hendpoint_alloc hwidth' hmask' setup.2.1 setup.2.2.1 setup.2.2.2
    hcounter hrow' hnode' (by omega) hencoded hrowExtent hparents'
  have hclock : steps q (treeSize q full) = 7 + outerClock (treeSize q full) (q + 2) := by
    simp only [steps, outerClock, budgetBlockClock_eq]
    ring
  rw [hclock, run_add]
  refine ⟨loop.active, loop.pc, loop.header, loop.counter, ?_, ?_, ?_, ?_, ?_⟩
  · intro budget hbudget
    rw [loop.good budget hbudget,
      rawGood_of_leading_frame full capWords _ state.heap initialized.heap (by omega) hq hs hroom hframe
        (by have hm := Nat.mul_le_mul_right (treeSize q full + 1) (show budget + 1 ≤ q + 2 by omega); nlinarith)]
  · intro budget hbudget
    rw [loop.bad budget hbudget,
      rawBad_of_leading_frame full capWords _ encoded state.heap initialized.heap (by omega) hq hs hroom hframe
        (by have hm := Nat.mul_le_mul_right (treeSize q full + 1) (show budget + 1 ≤ q + 2 by omega); nlinarith)
        hencoded hparents]
  · intro address hscratch hflags
    refine (loop.«outside» address hscratch hflags).trans ?_
    rw [setup.1, Function.update_of_ne (hscratch 8 (by decide) (by decide))]
  · intro physical hphysical
    exact (loop.leading physical hphysical).trans (hframe physical hphysical)
  · have hi : HighFrame endpoint state.heap initialized.heap := by
      rw [setup.1]
      exact update_high_frame endpoint (header + 8) state.heap _ hend
        (scratch_lt_endpoint workspace (treeSize q full) q 8 (by decide))
    exact hi.trans loop.high

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
