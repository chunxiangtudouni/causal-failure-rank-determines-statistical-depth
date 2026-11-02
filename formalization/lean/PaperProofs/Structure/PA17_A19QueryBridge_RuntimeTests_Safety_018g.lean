module
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Safety_018f

/-! Full fixed355-op Tests prefix safety. The outer entry classification is
itself derived from actual execution; callers supply no prefix/access oracle. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeTests010

theorem actual_outerLoop_safe {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords rowBase remaining encoded : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hendpoint_alloc : PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) q ≤ heapWords)
    (ready : OuterLoopEntry full configuration capWords rowBase encoded origin remaining state)
    (count : Nat) (hcut : count < outerClock (treeSize q full) remaining) :
    StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing count state) := by
  have classified := actual_outer_prefix_classification em full command configuration capWords heapWords rowBase remaining encoded state
    hb hq hw ready.core.rep bitmap hs hf hendpoint_alloc ready.core.width ready.core.mask ready.core.header
    ready.core.pc_eq ready.core.active ready.counter ready.row_pointer ready.node_pointer ready.remaining_bound
    ready.encoded_bound ready.row_extent ready.parents count hcut
  rcases classified with ⟨r, offset, entry, data, hoffset, hrun⟩ | ⟨b, offset, entry, data, hoffset, hrun⟩
  · rw [hrun]
    apply budgetTest_safe em _ _ heapWords entry data.core.header data.core.pc_eq data.core.active ?_ offset hoffset
    have he : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8 <
        PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q :=
      scratch_lt_endpoint _ _ _ 8 (by decide)
    exact he.trans_le hendpoint_alloc
  · rw [hrun]
    exact actual_budgetBlock_safe em full command configuration capWords heapWords rowBase b encoded entry hb hq hw
      bitmap hs hf hendpoint_alloc data offset hoffset

theorem actual_tests_prefix_safe {bits q origin : Nat} {containing : List PackingOp}
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
    (count : Nat) (hcut : count < steps q (treeSize q full)) :
    StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing count state) := by
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
  have hromq : (rom.words .input).getD 1 0 = q := rfl
  have hinput : 1 < rom.input.length := by
    change 1 < (([full.length, q] ++ incidence full) ++ [command.word]).length
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hslots : header + 8 < heapWords :=
    (scratch_lt_endpoint workspace (treeSize q full) q 8 (by decide)).trans_le hendpoint_alloc
  have setup := actual_setup em rom header q state hp ha hh hromq hqfit
  have hframe : ∀ physical < header + 8,
      initialized.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    intro physical hphysical
    rw [setup.1]
    exact update_leading_frame state.heap header 8 _ hroom (by decide) (by decide) physical hphysical
  have core : BudgetCoreReady full configuration capWords origin state := ⟨rep, hwidth, hmask, hh, hp, ha⟩
  have nextCore := core_after_leading full configuration capWords origin (origin + 7) state initialized core
    (by omega) hq bitmap hs hroom hframe setup.2.1 setup.2.2.1 setup.2.2.2
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
  have hclock : steps q (treeSize q full) = 7 + outerClock (treeSize q full) (q + 2) := by
    simp only [steps, outerClock, budgetBlockClock_eq]
    ring
  by_cases hsetup : count < 7
  · exact setup_safe em rom header heapWords state hh hp ha hslots hinput count hsetup
  · have hfront : packingRun rom containing count state = packingRun rom containing (count - 7) initialized := by
      conv_lhs => rw [show count = 7 + (count - 7) by omega]
      exact run_add rom containing 7 (count - 7) state
    rw [hfront]
    apply actual_outerLoop_safe em full command configuration capWords heapWords rowBase (q + 2) encoded initialized
      hb hq hw bitmap hs hf hendpoint_alloc
      ⟨nextCore, hcounter, hrow', hnode', by omega, hencoded, hrowExtent, hparents'⟩ (count - 7)
    rw [hclock] at hcut
    omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
