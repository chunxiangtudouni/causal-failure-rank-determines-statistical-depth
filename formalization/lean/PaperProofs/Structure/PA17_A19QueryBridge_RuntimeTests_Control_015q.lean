module
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015p

/-! Every real clock of setup plus all budgets preserves the exact physical
write-set complement. Incoming scratch is arbitrary; real setup initializes it. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem OuterFrame.high {bits q : Nat} {full : List (Finset (Fin q))} {capWords remaining : Nat}
    {old fresh : BitVec bits → BitVec bits} (frame : OuterFrame full capWords remaining old fresh)
    (hend : Fits bits (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q))
    (hr : remaining ≤ q + 2) :
    HighFrame (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q) old fresh := by
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  intro physical hp hge
  apply frame
  · intro offset _ ho
    exact high_address_ne _ _ physical hend (scratch_lt_endpoint workspace (treeSize q full) q offset (by omega)) hp hge
  · intro budget hbudget
    exact ⟨high_address_ne _ _ physical hend (good_lt_endpoint workspace (treeSize q full) q budget (by omega)) hp hge,
      high_address_ne _ _ physical hend (bad_lt_endpoint workspace (treeSize q full) q budget (by omega)) hp hge⟩

theorem OuterFrame.leading {bits q : Nat} {full : List (Finset (Fin q))} {capWords remaining : Nat}
    {old fresh : BitVec bits → BitVec bits} (frame : OuterFrame full capWords remaining old fresh)
    (hend : Fits bits (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q))
    (hr : remaining ≤ q + 2) :
    ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8,
      fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical) := by
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let endpoint := PSTRQueryLayout.endpoint workspace (treeSize q full) q
  intro physical hp
  have h8 : header + 8 < endpoint := scratch_lt_endpoint workspace (treeSize q full) q 8 (by decide)
  have hpf : Fits bits physical := (hp.trans h8).trans hend
  have hne (target : Nat) (ht : target < endpoint) (hpt : physical < target) :
      BitVec.ofNat bits physical ≠ BitVec.ofNat bits target := by
    intro heq
    have hn := (ofNat_injective_of_fit physical target hpf (ht.trans hend)).mp heq
    omega
  apply frame
  · intro offset ho hu
    exact hne _ (scratch_lt_endpoint workspace (treeSize q full) q offset (by omega)) (by omega)
  · intro budget hbudget
    exact ⟨hne _ (good_lt_endpoint workspace (treeSize q full) q budget (by omega)) (by omega),
      hne _ (bad_lt_endpoint workspace (treeSize q full) q budget (by omega)) (by omega)⟩

theorem actual_tests_prefix_frame {bits q origin : Nat} {containing : List PackingOp}
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
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full)
    (count : Nat) (hcut : count ≤ steps q (treeSize q full)) :
    OuterFrame full capWords (q + 2) state.heap
      (packingRun (callInput q full command) containing count state).heap := by
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
  have setupPost := actual_setup em rom header q state hp ha hh hromq hqfit
  have hframe : ∀ physical < header + 8, initialized.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    intro physical hphysical
    rw [setupPost.1]
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
    rw [setupPost.1, Function.update_self]
  have hlogical := logical_leading_frame full capWords (treeSize q full) state.heap initialized.heap
    (by omega) hq hs hroom hframe
  have hparents' : ∀ e ≤ treeSize q full, logicalHeap q capWords initialized.heap
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full := by
    intro e he
    rw [hlogical _ (by unfold PSTRQueryLayout.header; omega)]
    exact hparents e he
  have hclock : steps q (treeSize q full) = 7 + outerClock (treeSize q full) (q + 2) := by
    simp only [steps, outerClock, budgetBlockClock_eq]
    ring
  intro address hscratch hflags
  by_cases hsetup : count ≤ 7
  · rw [actual_setup_prefix em rom state hp ha count hsetup]
    interval_cases count <;>
      simp +decide [setup, storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
        hh, BitVec.ofNat_add_ofNat, Function.update_of_ne (hscratch 8 (by decide) (by decide))]
  · have hfront : packingRun rom containing count state = packingRun rom containing (count - 7) initialized := by
      conv_lhs => rw [show count = 7 + (count - 7) by omega]
      exact run_add rom containing 7 (count - 7) state
    rw [hfront]
    have lower := actual_budgetLoop_prefix_frame em full command configuration capWords heapWords rowBase (q + 2) encoded initialized
      hb hq hw hrep bitmap hs hf hendpoint_alloc hwidth' hmask' setupPost.2.1 setupPost.2.2.1 setupPost.2.2.2
      hcounter hrow' hnode' (by omega) hencoded hrowExtent hparents' (count - 7)
      (by rw [hclock] at hcut; omega)
    refine (lower address hscratch hflags).trans ?_
    rw [setupPost.1, Function.update_of_ne (hscratch 8 (by decide) (by decide))]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
