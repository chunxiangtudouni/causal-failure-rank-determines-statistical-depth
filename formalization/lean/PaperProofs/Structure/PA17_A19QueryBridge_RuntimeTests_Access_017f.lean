module
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Access_017e
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010m

/-! Real86 budget entry and109 ancestor kernel EVERY-prefix access. Their
scratch initialization is executed, and the58-op reader is the actual
packed reader using the same original logical heap and saved width. -/
@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeTests010

theorem budgetInit_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords rowBase budget : Nat)
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
    (hc : state.register .total = BitVec.ofNat bits (budget + 1))
    (hr : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))) =
      BitVec.ofNat bits rowBase)
    (hscalar : rowBase + budget * (treeSize q full + 1) < capWords) :
    ∀ count (hcut : count < budgetInit.length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (budgetInit.take count) state) budgetInit[count] := by
  let rom := callInput q full command
  let header := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
  let scalar := rowBase + budget * (treeSize q full + 1)
  let lead := executeOps rom budgetLead state
  let read := executeOps rom PA17A19RuntimeRead007.cachedProgram lead
  have hslots : header + 15 < heapWords := by
    dsimp only [header]
    omega
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have ht : Fits bits (treeSize q full + 1) := (show treeSize q full + 1 ≤ header by
    unfold header PSTRQueryLayout.header; omega).trans_lt hheader
  have hwpos : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro hz
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp hz))
  have hm := Nat.mul_le_mul_left capWords (show 1 ≤ CapacityBits.width q from hwpos)
  have hcf : Fits bits capWords := (show capWords ≤ 4 + capWords * CapacityBits.width q by nlinarith).trans_lt hs
  have hbudgetC : budget < capWords := by
    have hm' := Nat.le_mul_of_pos_right budget (by omega : 0 < treeSize q full + 1)
    omega
  have hbudget : Fits bits (budget + 1) := (Nat.succ_le_of_lt hbudgetC).trans_lt hcf
  have hl := execute_budgetLead rom header budget rowBase (treeSize q full) state hroom hbudget ht hh hc rep.1 hr
  have hframe : ∀ physical < header + 8, lead.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    intro physical hp
    rw [hl.1]
    rw [update_leading_frame _ header 13 _ hroom (by decide) (by decide) physical hp]
    exact update_leading_frame _ header 8 _ hroom (by decide) (by decide) physical hp
  have readResult := cached_of_leading_frame full command configuration capWords heapWords scalar state lead
    hb hq hw rep bitmap hs hf halloc hframe hwidth hmask hl.2.2 hl.2.1 hscalar
  apply PA17A19RuntimeRead007.access_append rom heapWords (budgetLead ++ PA17A19RuntimeRead007.cachedProgram) tagTail state
  · exact PA17A19RuntimeRead007.access_append rom heapWords budgetLead PA17A19RuntimeRead007.cachedProgram state
      (budgetLead_access rom header heapWords state hh hslots)
      (cached_access_of_leading_frame full command configuration capWords heapWords scalar state lead
        hb hq hw rep bitmap hs hf halloc hframe hwidth hl.2.2 hl.2.1 hscalar)
  · simpa only [executeOps_append] using tagTail_access rom header heapWords read readResult.1 hslots

theorem ancestorKernel_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
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
    ∀ count (hcut : count < ancestorKernel.length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (ancestorKernel.take count) state) ancestorKernel[count] := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let lead := executeOps rom ancestorLead state
  let read := executeOps rom PA17A19RuntimeRead007.cachedProgram lead
  have hslots : header + 15 < heapWords := by
    dsimp only [header, workspace]
    omega
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
  have readResult := cached_of_leading_frame full command configuration capWords heapWords
    (entryBase + 1 + (encoded - 1)) state lead hb hq hw rep bitmap hs hf halloc hframe hwidth hmask
    hl.2.2 hl.2.1 hscalar
  have hsize : (read.heap (BitVec.ofNat bits 0)).toNat = treeSize q full := by
    rw [show read.heap = lead.heap from readResult.2.2, hframe 0 (by omega)]
    exact rep.1
  have hne11 : BitVec.ofNat bits (header + 11) ≠ BitVec.ofNat bits (header + 12) := by
    intro hh'
    have h := (slots_eq_iff header 11 12 hroom (by decide) (by decide)).mp hh'
    omega
  have hnodecell : read.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits encoded := by
    rw [show read.heap = lead.heap from readResult.2.2, hl.1, Function.update_of_ne hne11]
    exact ha
  apply PA17A19RuntimeRead007.access_append rom heapWords (ancestorLead ++ PA17A19RuntimeRead007.cachedProgram) ancestorTail state
  · exact PA17A19RuntimeRead007.access_append rom heapWords ancestorLead PA17A19RuntimeRead007.cachedProgram state
      (ancestorLead_access rom header heapWords state hh hslots)
      (cached_access_of_leading_frame full command configuration capWords heapWords
        (entryBase + 1 + (encoded - 1)) state lead hb hq hw rep bitmap hs hf halloc hframe hwidth
        hl.2.2 hl.2.1 hscalar)
  · simpa only [executeOps_append] using
      ancestorTail_access rom workspace (treeSize q full) encoded heapWords read (by omega) hroom
        hsize readResult.1 hnodecell (by omega) hn hslots

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsAccess017
