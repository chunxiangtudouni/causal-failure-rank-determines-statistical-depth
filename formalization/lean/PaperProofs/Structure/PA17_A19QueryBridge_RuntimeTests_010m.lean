module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010k
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010l

/-! The fixed86-op budget entry computes its logical row address, saves it,
executes the genuine packed reader, initializes the tag flag and node counter.
No initial H8..15 content or predecoded tag is supplied by the caller. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem budgetInit_result {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
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
    let header := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
    let scalar := rowBase + budget * (treeSize q full + 1)
    let flag := BitVec.ofNat bits (if logicalHeap q capWords state.heap scalar = 0 then 0 else 1)
    let after := executeOps (callInput q full command) budgetInit state
    after.heap = Function.update
      (Function.update
        (Function.update
          (Function.update state.heap (BitVec.ofNat bits (header + 8)) (BitVec.ofNat bits budget))
          (BitVec.ofNat bits (header + 13)) (BitVec.ofNat bits scalar))
        (BitVec.ofNat bits (header + 10)) flag)
      (BitVec.ofNat bits (header + 9)) (BitVec.ofNat bits (treeSize q full)) ∧
      after.register .address = BitVec.ofNat bits header := by
  let rom := callInput q full command
  let header := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
  let scalar := rowBase + budget * (treeSize q full + 1)
  let lead := executeOps rom budgetLead state
  let read := executeOps rom PA17A19RuntimeRead007.cachedProgram lead
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have ht : Fits bits (treeSize q full + 1) := (show treeSize q full + 1 ≤ header by
    unfold header PSTRQueryLayout.header; omega).trans_lt hheader
  have htf : Fits bits (treeSize q full) := (Nat.le_add_right (treeSize q full) 1).trans_lt ht
  have hwpos : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro hz
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp hz))
  have hm := Nat.mul_le_mul_left capWords (show 1 ≤ CapacityBits.width q from hwpos)
  have hcf : Fits bits capWords := (show capWords ≤ 4 + capWords * CapacityBits.width q by nlinarith).trans_lt hs
  have hbudgetC : budget < capWords := by
    have hm' := Nat.le_mul_of_pos_right budget (by omega : 0 < treeSize q full + 1)
    omega
  have hbudget : Fits bits (budget + 1) := (Nat.succ_le_of_lt hbudgetC).trans_lt hcf
  have hsizeWord : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits (treeSize q full) := by
    apply BitVec.eq_of_toNat_eq
    rw [rep.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htf]
  have hl := execute_budgetLead rom header budget rowBase (treeSize q full) state hroom hbudget ht hh hc rep.1 hr
  have hframe : ∀ physical < header + 8, lead.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    intro physical hp
    rw [hl.1]
    rw [update_leading_frame _ header 13 _ hroom (by decide) (by decide) physical hp]
    exact update_leading_frame _ header 8 _ hroom (by decide) (by decide) physical hp
  have hr' := cached_of_leading_frame full command configuration capWords heapWords scalar state lead
    hb hq hw rep bitmap hs hf halloc hframe hwidth hmask hl.2.2 hl.2.1 hscalar
  have ht' := execute_tagTail rom header read hroom hr'.1
  have hzero : read.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits (treeSize q full) := by
    rw [hr'.2.2, hframe 0 (by omega)]
    exact hsizeWord
  simpa only [budgetInit, executeOps_append, rom, read, lead, hr'.2.1, hzero,
    hr'.2.2, hl.1] using ht'

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
