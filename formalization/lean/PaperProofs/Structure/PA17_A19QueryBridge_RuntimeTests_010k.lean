module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010h

/-! Fixed actual ancestor iteration: a genuine fuel store, fixed58-op packed
read, strict count comparison, and actual sentinel-parent heap load. The
leading frame is proved from the executed store, not assumed at this API. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem cached_of_leading_frame {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
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
    (hmask : before.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (hh : entry.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hv : entry.register .value = BitVec.ofNat bits scalar) (hscalar : scalar < capWords) :
    let after := executeOps (callInput q full command) PA17A19RuntimeRead007.cachedProgram entry
    after.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)) ∧
      (after.register .value).toNat = logicalHeap q capWords before.heap scalar ∧ after.heap = entry.heap := by
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
  have hcache (offset : Nat) (ho : offset ≤ 13) : workspace + offset < header + 8 := by
    unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have hr := PA17A19RuntimeRead007.execute_cached full command configuration capWords heapWords entry
    hb hq hw hrep (by rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsf]; exact hscalar)
    hs hf (by omega) ((hframe _ (hcache 12 (by decide))).trans hwidth)
    ((hframe _ (hcache 13 (by decide))).trans hmask) hh
  refine ⟨hr.1, ?_, hr.2.2.1⟩
  have hv' := hr.2.1
  rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsf] at hv'
  exact hv'.trans (logical_scalar_of_leading_frame full capWords scalar before.heap entry.heap
    (by omega) hq hs hroom hframe hscalar)

def ancestorKernel : List PackingOp := ancestorLead ++ PA17A19RuntimeRead007.cachedProgram ++ ancestorTail

theorem ancestorKernel_length : ancestorKernel.length = 109 := rfl

theorem ancestorKernel_result {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase remaining encoded : Nat)
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
    (hc : state.register .total = BitVec.ofNat bits (remaining + 1))
    (he : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
      BitVec.ofNat bits entryBase)
    (ha : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 11)) =
      BitVec.ofNat bits encoded)
    (hr : remaining < treeSize q full) (hn : encoded ≤ treeSize q full)
    (hscalar : entryBase + 1 + (encoded - 1) < capWords) :
    let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
    let header := PSTRQueryLayout.header workspace (treeSize q full)
    let after := executeOps (callInput q full command) ancestorKernel state
    let flag := if encoded = 0 then state.heap (BitVec.ofNat bits (header + 14))
      else if (state.heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace + (encoded - 1)))).toNat <
          logicalHeap q capWords state.heap (entryBase + 1 + (encoded - 1))
        then state.heap (BitVec.ofNat bits (header + 14)) else BitVec.ofNat bits 0
    after.heap = Function.update
      (Function.update
        (Function.update state.heap (BitVec.ofNat bits (header + 12)) (BitVec.ofNat bits remaining))
        (BitVec.ofNat bits (header + 14)) flag)
      (BitVec.ofNat bits (header + 11))
      (state.heap (BitVec.ofNat bits (PSTRQueryLayout.parentsBase workspace (treeSize q full) + encoded))) ∧
      after.register .address = BitVec.ofNat bits header := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let lead := executeOps rom ancestorLead state
  let read := executeOps rom PA17A19RuntimeRead007.cachedProgram lead
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have hremain : Fits bits (remaining + 1) := (show remaining + 1 ≤ header by
    unfold header PSTRQueryLayout.header; omega).trans_lt hheader
  have hencoded : Fits bits encoded := (show encoded ≤ header by
    unfold header PSTRQueryLayout.header; omega).trans_lt hheader
  have hl := execute_ancestorLead rom header remaining entryBase encoded state hroom hremain hencoded hh hc he ha
  have hframe : ∀ physical < header + 8, lead.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    intro physical hp
    rw [hl.1]
    exact update_leading_frame state.heap header 12 _ hroom (by decide) (by decide) physical hp
  have hc' := cached_of_leading_frame full command configuration capWords heapWords
    (entryBase + 1 + (encoded - 1)) state lead hb hq hw rep bitmap hs hf halloc hframe hwidth hmask
    hl.2.2 hl.2.1 hscalar
  have hreadheap : read.heap = lead.heap := hc'.2.2
  have hreadvalue : (read.register .value).toNat = logicalHeap q capWords state.heap (entryBase + 1 + (encoded - 1)) := hc'.2.1
  have hsize : (read.heap (BitVec.ofNat bits 0)).toNat = treeSize q full := by
    rw [hreadheap, hframe 0 (by omega)]
    exact rep.1
  have hne11 : BitVec.ofNat bits (header + 11) ≠ BitVec.ofNat bits (header + 12) := by
    intro hh'
    have h := (slots_eq_iff header 11 12 hroom (by decide) (by decide)).mp hh'
    omega
  have hne14 : BitVec.ofNat bits (header + 14) ≠ BitVec.ofNat bits (header + 12) := by
    intro hh'
    have h := (slots_eq_iff header 14 12 hroom (by decide) (by decide)).mp hh'
    omega
  have hnodecell : read.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits encoded := by
    rw [hreadheap, hl.1, Function.update_of_ne hne11]
    exact ha
  have ht := execute_ancestorTail rom workspace (treeSize q full) encoded read (by omega) hroom hsize hc'.1 hnodecell hn
  have hcount : read.heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace + (encoded - 1))) =
      state.heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase workspace + (encoded - 1))) := by
    rw [hreadheap]
    apply hframe
    unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have hparent : read.heap (BitVec.ofNat bits (PSTRQueryLayout.parentsBase workspace (treeSize q full) + encoded)) =
      state.heap (BitVec.ofNat bits (PSTRQueryLayout.parentsBase workspace (treeSize q full) + encoded)) := by
    rw [hreadheap]
    exact hframe _ (by
      have h := parent_encoded_lt_header workspace (treeSize q full) encoded hn
      omega)
  have hflag : read.heap (BitVec.ofNat bits (header + 14)) = state.heap (BitVec.ofNat bits (header + 14)) := by
    rw [hreadheap, hl.1, Function.update_of_ne hne14]
  dsimp only [header, workspace] at ht hcount hparent hflag hne14
  simpa only [ancestorKernel, executeOps_append, rom, read, lead, hcount, hparent,
    hreadvalue, hflag, hreadheap, hl.1, Function.update_of_ne hne14] using ht

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
