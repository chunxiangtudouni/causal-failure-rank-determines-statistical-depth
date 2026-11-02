module

public import Structure.PA17_A19QueryBridge_RuntimeTests_Access_017d
public import Structure.PA17_A19QueryBridge_RuntimeTests_010k

/-! Actual prefix access for the fixed90-op node kernel, composing the
executed scratch store with the actual58-op cached reader and count tail. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeTests010

theorem cached_access_of_leading_frame {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords scalar : Nat)
    (before entry : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration before.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16 < heapWords)
    (hframe : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 8, entry.heap (BitVec.ofNat bits physical) = before.heap (BitVec.ofNat bits physical))
    (hwidth : before.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hh : entry.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hv : entry.register .value = BitVec.ofNat bits scalar) (hscalar : scalar < capWords) :
    ∀ count (hc : count < PA17A19RuntimeRead007.cachedProgram.length),
      packingAccessFits (callInput q full command) heapWords
        (executeOps (callInput q full command) (PA17A19RuntimeRead007.cachedProgram.take count) entry)
        PA17A19RuntimeRead007.cachedProgram[count] := by
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hrep := represents_of_leading_frame full configuration capWords before.heap entry.heap
    (by omega) hq rep bitmap hs hroom hframe
  have hwpos : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro hz
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp hz))
  have hm := Nat.mul_le_mul_left capWords (show 1 ≤ CapacityBits.width q from hwpos)
  have hcf : Fits bits capWords := (show capWords ≤ 4 + capWords * CapacityBits.width q by nlinarith).trans_lt hs
  have hsf : Fits bits scalar := hscalar.trans hcf
  have hcache : workspace + 12 < header + 8 := by
    unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  exact PA17A19RuntimeRead007.cached_access_prefix full command configuration capWords heapWords entry
    hb hq hw hrep (by rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsf]; exact hscalar)
    hs hf (by omega) ((hframe _ hcache).trans hwidth) hh

theorem nodeKernel_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
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
    ∀ count (hcut : count < nodeKernel.length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (nodeKernel.take count) state) nodeKernel[count] := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let lead := executeOps rom nodeLead state
  let read := executeOps rom PA17A19RuntimeRead007.cachedProgram lead
  have hslots : header + 15 < heapWords := by
    dsimp only [header, workspace]
    omega
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have hnode : Fits bits (node + 1) := (show node + 1 ≤ header from by
    unfold header PSTRQueryLayout.header; omega).trans_lt hheader
  have hl := execute_nodeLead rom header node entryBase state hroom hnode hh hc he
  have hframe : ∀ physical < header + 8, lead.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    intro physical hp
    rw [hl.1]
    exact update_leading_frame state.heap header 9 _ hroom (by decide) (by decide) physical hp
  have hr := cached_of_leading_frame full command configuration capWords heapWords (entryBase + 1 + node)
    state lead hb hq hw rep bitmap hs hf halloc hframe hwidth hmask hl.2.2 hl.2.1 hscalar
  have hsize : (read.heap (BitVec.ofNat bits 0)).toNat = treeSize q full := by
    rw [show read.heap = lead.heap from hr.2.2, hframe 0 (by omega)]
    exact rep.1
  have hnodecell : read.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits node := by
    rw [show read.heap = lead.heap from hr.2.2, hl.1, Function.update_self]
  apply PA17A19RuntimeRead007.access_append rom heapWords (nodeLead ++ PA17A19RuntimeRead007.cachedProgram)
    PA17A19RuntimeTests010.nodeTail state
  · exact PA17A19RuntimeRead007.access_append rom heapWords nodeLead PA17A19RuntimeRead007.cachedProgram state
      (nodeLead_access rom header heapWords state hh hslots)
      (cached_access_of_leading_frame full command configuration capWords heapWords (entryBase + 1 + node)
        state lead hb hq hw rep bitmap hs hf halloc hframe hwidth hl.2.2 hl.2.1 hscalar)
  · simpa only [executeOps_append] using
      nodeTail_access rom workspace (treeSize q full) node heapWords read (by omega) hheader hsize
        hr.1 hnodecell hn hslots

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
