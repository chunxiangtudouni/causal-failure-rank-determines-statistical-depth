module

public import Structure.PA17_A19QueryBridge_RuntimeTests_010c
public import Structure.PA17_A19QueryBridge_RuntimeTests_010e
public import Structure.PA17_A19QueryBridge_RuntimeTests_010f

/-! Same-call packed-reader composition for a genuine reverse-node step.
The table scalar is read by the fixed58-op program from the original packed
heap after actual counter stores. No capacity answer or prefix-safety oracle
is an input. This is a single-node component, not the complete tests loop. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem update_leading_frame {bits : Nat} (heap : BitVec bits → BitVec bits) (header offset : Nat)
    (value : BitVec bits) (hroom : Fits bits (header + 16)) (ho : 8 ≤ offset) (hu : offset < 16)
    (physical : Nat) (hp : physical < header + 8) :
    (Function.update heap (BitVec.ofNat bits (header + offset)) value) (BitVec.ofNat bits physical) =
      heap (BitVec.ofNat bits physical) := by
  apply Function.update_of_ne
  intro he
  have hn := (ofNat_injective_of_fit _ _ ((show physical ≤ header + 16 by omega).trans_lt hroom)
    ((show header + offset ≤ header + 16 by omega).trans_lt hroom)).mp he
  omega

theorem represents_of_leading_frame {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (old fresh : BitVec bits → BitVec bits)
    (hb : 0 < bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration old)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16))
    (hframe : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 8, fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical)) :
    HeapRepresents q full capWords configuration fresh := by
  let header := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
  refine PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (header + 8)
    old fresh hb hq rep bitmap hr ((show header + 8 + 3 ≤ header + 16 by omega).trans_lt hroom) ?_ hframe
  unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    PSTRQueryLayout.physicalWorkspace PSTRStaticHeap.metadataAddress
  omega

theorem logical_scalar_of_leading_frame {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords scalar : Nat) (old fresh : BitVec bits → BitVec bits)
    (hb : 0 < bits) (hq : 0 < q) (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16))
    (hframe : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 8, fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical))
    (hs : scalar < capWords) : logicalHeap q capWords fresh scalar = logicalHeap q capWords old scalar := by
  let header := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
  refine PSTRRepairHeap.logical_frame old fresh capWords 0 (header + 8) scalar hb hq hr
    ((show header + 8 + 3 ≤ header + 16 by omega).trans_lt hroom) ?_ hframe (by omega)
  unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    PSTRQueryLayout.physicalWorkspace PSTRStaticHeap.metadataAddress
  omega

def nodeKernel : List PackingOp := nodeLead ++ PA17A19RuntimeRead007.cachedProgram ++ nodeTail

theorem nodeKernel_length : nodeKernel.length = 90 := rfl

theorem nodeKernel_result {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase node : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
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
    (hc : state.register .total = BitVec.ofNat bits (node + 1))
    (he : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
      BitVec.ofNat bits entryBase)
    (hn : node < treeSize q full) (hscalar : entryBase + 1 + node < capWords) :
    let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
    let header := PSTRQueryLayout.header workspace (treeSize q full)
    let after := executeOps (callInput q full command) nodeKernel state
    let flag := if (state.heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace + node))).toNat ≤
        logicalHeap q capWords state.heap (entryBase + 1 + node)
      then state.heap (BitVec.ofNat bits (header + 10)) else BitVec.ofNat bits 0
    after.heap = Function.update
      (Function.update state.heap (BitVec.ofNat bits (header + 9)) (BitVec.ofNat bits node))
      (BitVec.ofNat bits (header + 10)) flag ∧ after.register .address = BitVec.ofNat bits header := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let lead := executeOps rom nodeLead state
  let read := executeOps rom PA17A19RuntimeRead007.cachedProgram lead
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have hnode : Fits bits (node + 1) := (show node + 1 ≤ header by
    unfold header PSTRQueryLayout.header; omega).trans_lt hheader
  have hl := execute_nodeLead rom header node entryBase state hroom hnode hh hc he
  have hframe : ∀ physical < header + 8, lead.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    intro physical hp
    rw [hl.1]
    exact update_leading_frame state.heap header 9 _ hroom (by decide) (by decide) physical hp
  have hrep : HeapRepresents q full capWords configuration lead.heap :=
    represents_of_leading_frame full configuration capWords state.heap lead.heap (by omega) hq rep bitmap hs hroom hframe
  have hwpos : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro hz
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp hz))
  have hm := Nat.mul_le_mul_left capWords (show 1 ≤ CapacityBits.width q from hwpos)
  have hcf : Fits bits capWords := (show capWords ≤ 4 + capWords * CapacityBits.width q by nlinarith).trans_lt hs
  have hsf : Fits bits (entryBase + 1 + node) := hscalar.trans hcf
  have hcache (offset : Nat) (ho : offset ≤ 13) : workspace + offset < header + 8 := by
    unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have hr := PA17A19RuntimeRead007.execute_cached full command configuration capWords heapWords lead
    hb hq hw hrep (by rw [hl.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsf]; exact hscalar)
    hs hf (by omega) ((hframe _ (hcache 12 (by decide))).trans hwidth)
    ((hframe _ (hcache 13 (by decide))).trans hmask) hl.2.2
  have hreadheap : read.heap = lead.heap := hr.2.2.1
  have hreadvalue : (read.register .value).toNat = logicalHeap q capWords state.heap (entryBase + 1 + node) := by
    have hh' := hr.2.1
    rw [hl.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsf] at hh'
    exact hh'.trans (logical_scalar_of_leading_frame full capWords (entryBase + 1 + node)
      state.heap lead.heap (by omega) hq hs hroom hframe hscalar)
  have hsize : (read.heap (BitVec.ofNat bits 0)).toNat = treeSize q full := by
    rw [hreadheap, hframe 0 (by omega)]
    exact rep.1
  have hnodecell : read.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits node := by
    rw [hreadheap, hl.1, Function.update_self]
  have ht := execute_nodeTail rom workspace (treeSize q full) node read (by omega) hheader hsize hr.1 hnodecell
  have hcount : read.heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace + node)) =
      state.heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace + node)) := by
    rw [hreadheap]
    exact hframe _ (by
      have hh' := counts_node_lt_header workspace (treeSize q full) node hn
      omega)
  have hne : BitVec.ofNat bits (header + 10) ≠ BitVec.ofNat bits (header + 9) := by
    intro hh'
    have hh'' := (slots_eq_iff header 10 9 hroom (by decide) (by decide)).mp hh'
    omega
  have hflag : read.heap (BitVec.ofNat bits (header + 10)) = state.heap (BitVec.ofNat bits (header + 10)) := by
    rw [hreadheap, hl.1, Function.update_of_ne hne]
  dsimp only [header, workspace] at ht hcount hflag hne
  simpa only [nodeKernel, executeOps_append, rom, read, lead, hcount, hreadvalue,
    hflag, hreadheap, hl.1, Function.update_of_ne hne] using ht

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
