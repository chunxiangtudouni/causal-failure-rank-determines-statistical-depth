module
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Safety_018g
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015n
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015q

/-! Complete safety certificate for the fixed355-op Tests in its original
containing execution. Exit is ACTIVE; the HD control/output region is framed
at every actual prefix, including the exit. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeTests010

structure TestsSafe {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (capWords heapWords origin : Nat) (containing : List PackingOp) (state : WordState bits) : Prop where
  active : (packingRun (callInput q full command) containing (steps q (treeSize q full)) state).halted = false
  pc : (packingRun (callInput q full command) containing (steps q (treeSize q full)) state).pc =
    BitVec.ofNat bits (5 * (origin + 355))
  prefix_safe : ∀ count < steps q (treeSize q full),
    StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing count state)
  leading : ∀ count ≤ steps q (treeSize q full),
    ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8,
      (packingRun (callInput q full command) containing count state).heap (BitVec.ofNat bits physical) =
        state.heap (BitVec.ofNat bits physical)
  high : ∀ count ≤ steps q (treeSize q full),
    HighFrame (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q)
      state.heap (packingRun (callInput q full command) containing count state).heap

theorem actual_tests_safe {bits q origin : Nat} {containing : List PackingOp}
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
    TestsSafe full command capWords heapWords origin containing state := by
  have result := actual_tests_from_materialized_header em full command configuration capWords heapWords rowBase encoded state
    hb hq hw rep bitmap hs hf hendpoint_alloc hwidth hmask hh hp ha hrowPointer hnodePointer hencoded hrowExtent hparents
  refine ⟨result.active, result.pc, ?_, ?_, ?_⟩
  · exact actual_tests_prefix_safe em full command configuration capWords heapWords rowBase encoded state
      hb hq hw rep bitmap hs hf hendpoint_alloc hwidth hmask hh hp ha hrowPointer hnodePointer hencoded hrowExtent hparents
  · intro count hc
    exact (actual_tests_prefix_frame em full command configuration capWords heapWords rowBase encoded state
      hb hq hw rep bitmap hs hf hendpoint_alloc hwidth hmask hh hp ha hrowPointer hnodePointer hencoded hrowExtent hparents count hc).leading
      (hendpoint_alloc.trans_lt hf) (by omega)
  · intro count hc
    exact (actual_tests_prefix_frame em full command configuration capWords heapWords rowBase encoded state
      hb hq hw rep bitmap hs hf hendpoint_alloc hwidth hmask hh hp ha hrowPointer hnodePointer hencoded hrowExtent hparents count hc).high
      (hendpoint_alloc.trans_lt hf) (by omega)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
