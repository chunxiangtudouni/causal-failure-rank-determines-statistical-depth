module
public import Structure.PA17_A19QueryBridge_RuntimeTests_Control_015k

/-! Every actual86-op budget-entry prefix preserves all Word cells outside
H8/H9/H10/H13; original scalar bounds restore the actual reader header. -/
@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem actual_budgetInit_prefix_frame {bits q origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
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
    (hscalar : rowBase + budget * (treeSize q full + 1) < capWords)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 12))) (hactive : state.halted = false)
    (address : BitVec bits)
    (h8 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8))
    (h9 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 9))
    (h10 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 10))
    (h13 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13))
    (count : Nat) (hcut : count ≤ 86) :
    (packingRun (callInput q full command) containing count state).heap address = state.heap address := by
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
  rw [actual_budgetInit_prefix em rom state hp hactive count hcut]
  change (executeOps rom ((budgetLead ++ PA17A19RuntimeRead007.cachedProgram ++ tagTail).take count) state).heap address = state.heap address
  apply executeOps_prefix_frame_append rom (budgetLead ++ PA17A19RuntimeRead007.cachedProgram) tagTail state address
  · intro cut hcut'
    apply executeOps_prefix_frame_append rom budgetLead PA17A19RuntimeRead007.cachedProgram state address
    · intro index hi
      exact budgetLead_prefix_frame rom header state hh address h8 h13 index (by simpa only [budgetLead_length] using hi)
    · intro index _
      rw [executeOps_prefix_noStore rom PA17A19RuntimeRead007.cachedProgram lead
        PA17A19RuntimeRead007.cachedProgram_noStore index]
    · exact hcut'
  · intro cut hcut'
    change (executeOps rom (tagTail.take cut) read).heap address = read.heap address
    exact tagTail_prefix_frame rom header read hr'.1 address h10 h9 cut
      (by simpa only [tagTail_length] using hcut')
  · change count ≤ budgetInit.length
    rw [budgetInit_length]
    exact hcut

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
