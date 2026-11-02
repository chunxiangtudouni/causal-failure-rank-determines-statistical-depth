module

public import Structure.PA17_A19QueryBridge_RuntimeTests_Control_015c

/-! Prefix assembly for actual execution. Local frame lemmas below concern
real executed prefixes and contain no safety or answer oracle. -/

@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem executeOps_prefix_split {bits : Nat} (rom : PhysicalROM) (left right : List PackingOp)
    (state : WordState bits) (count : Nat) :
    executeOps rom ((left ++ right).take count) state =
      if count ≤ left.length then executeOps rom (left.take count) state else
        executeOps rom (right.take (count - left.length)) (executeOps rom left state) := by
  rw [List.take_append, executeOps_append]
  split_ifs with hc
  · rw [Nat.sub_eq_zero_of_le hc]; rfl
  · have hl : left.take count = left := List.take_of_length_le (by omega)
    rw [hl]

theorem executeOps_prefix_frame_append {bits : Nat} (rom : PhysicalROM) (left right : List PackingOp)
    (state : WordState bits) (address : BitVec bits)
    (hl : ∀ count ≤ left.length, (executeOps rom (left.take count) state).heap address = state.heap address)
    (hr : ∀ count ≤ right.length,
      (executeOps rom (right.take count) (executeOps rom left state)).heap address =
        (executeOps rom left state).heap address)
    (count : Nat) (hc : count ≤ (left ++ right).length) :
    (executeOps rom ((left ++ right).take count) state).heap address = state.heap address := by
  rw [executeOps_prefix_split]
  split_ifs with hle
  · exact hl count hle
  · have hh := hl left.length (by omega)
    rw [List.take_length] at hh
    exact (hr (count - left.length) (by simp only [List.length_append] at hc; omega)).trans hh

theorem executeOps_prefix_noStore {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (hno : ∀ op ∈ program, HeapPreservingOp op) (count : Nat) :
    (executeOps rom (program.take count) state).heap = state.heap := by
  apply executeOps_heap_of_no_store
  intro op hop
  exact hno op (List.mem_of_mem_take hop)

theorem singleSlot_prefix_frame {bits : Nat} (rom : PhysicalROM)
    (before after : List PackingOp) (header offset : Nat) (source : Register) (state : WordState bits)
    (hbefore : ∀ op ∈ before, HeapPreservingOp op) (hafter : ∀ op ∈ after, HeapPreservingOp op)
    (hh : (executeOps rom before state).register .address = BitVec.ofNat bits header)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (header + offset))
    (count : Nat) (hc : count ≤ (before ++ storeSlot offset source ++ after).length) :
    (executeOps rom ((before ++ storeSlot offset source ++ after).take count) state).heap address =
      state.heap address := by
  apply executeOps_prefix_frame_append rom (before ++ storeSlot offset source) after state address
  · intro cut hcut
    apply executeOps_prefix_frame_append rom before (storeSlot offset source) state address
    · intro index _
      rw [executeOps_prefix_noStore rom before state hbefore index]
    · intro index hi
      exact storeSlot_prefix_frame rom offset header source (executeOps rom before state) hh address hne index
        (by simpa only [storeSlot_length] using hi)
    · exact hcut
  · intro cut _
    rw [executeOps_prefix_noStore rom after (executeOps rom (before ++ storeSlot offset source) state) hafter cut]
  · exact hc

theorem ancestorLead_prefix_frame {bits : Nat} (rom : PhysicalROM) (header : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (header + 12))
    (count : Nat) (hc : count ≤ 15) :
    (executeOps rom (ancestorLead.take count) state).heap address = state.heap address := by
  let before := ancestorLead.take 2
  let after := ancestorLead.drop 5
  have heq : ancestorLead = before ++ storeSlot 12 .total ++ after := rfl
  rw [heq]
  apply singleSlot_prefix_frame rom before after header 12 .total state
  · simp [before, ancestorLead, HeapPreservingOp]
  · simp [after, ancestorLead, loadSlot, storeSlot, HeapPreservingOp]
  · simp +decide [before, ancestorLead, executeOps, packingExecuteOp, wordOp, wordInstruction, hh]
  · exact hne
  · rw [← heq, ancestorLead_length]; exact hc

theorem extensionCompare_prefix_frame {bits : Nat} (rom : PhysicalROM) (header : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (header + 14))
    (count : Nat) (hc : count ≤ 13) :
    (executeOps rom (extensionCompare.take count) state).heap address = state.heap address := by
  let before := extensionCompare.take 10
  have heq : extensionCompare = before ++ storeSlot 14 .flag ++ [] := rfl
  rw [heq]
  apply singleSlot_prefix_frame rom before [] header 14 .flag state
  · simp [before, extensionCompare, loadSlot, HeapPreservingOp]
  · simp
  · simp +decide [before, extensionCompare, loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, hh]
  · exact hne
  · rw [← heq, extensionCompare_length]; exact hc

theorem parentTail_prefix_frame {bits : Nat} (rom : PhysicalROM) (header : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (header + 11))
    (count : Nat) (hc : count ≤ 10) :
    (executeOps rom (parentTail.take count) state).heap address = state.heap address := by
  let before := parentTail.take 7
  have heq : parentTail = before ++ storeSlot 11 .fresh ++ [] := rfl
  rw [heq]
  apply singleSlot_prefix_frame rom before [] header 11 .fresh state
  · simp [before, parentTail, HeapPreservingOp]
  · simp
  · simp +decide [before, parentTail, executeOps, packingExecuteOp, wordOp, wordInstruction, hh]
  · exact hne
  · rw [← heq, parentTail_length]; exact hc

def budgetClock (size : Nat) : Nat := 138 + 215 * size

theorem budgetClock_phases (size : Nat) :
    budgetClock size = 86 + ((5 + 98 * size) + (26 + (ancestorClock size + 16))) := by
  unfold budgetClock ancestorClock
  omega

theorem run_prefix_split {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (state : WordState bits) (first count : Nat) :
    packingRun rom containing count state = if count ≤ first then packingRun rom containing count state else
      packingRun rom containing (count - first) (packingRun rom containing first state) := by
  split_ifs with hc
  · rfl
  · conv_lhs => rw [show count = first + (count - first) by omega]
    exact run_add rom containing first (count - first) state

theorem actual_budget_prefix_split {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (size : Nat) (state : WordState bits) (count : Nat) :
    let init := packingRun rom containing 86 state
    let nodes := packingRun rom containing (5 + 98 * size) init
    let finish := packingRun rom containing 26 nodes
    let ancestors := packingRun rom containing (ancestorClock size) finish
    packingRun rom containing count state =
      if count ≤ 86 then packingRun rom containing count state else
      if count - 86 ≤ 5 + 98 * size then packingRun rom containing (count - 86) init else
      if count - 86 - (5 + 98 * size) ≤ 26 then
        packingRun rom containing (count - 86 - (5 + 98 * size)) nodes else
      if count - 86 - (5 + 98 * size) - 26 ≤ ancestorClock size then
        packingRun rom containing (count - 86 - (5 + 98 * size) - 26) finish else
        packingRun rom containing (count - 86 - (5 + 98 * size) - 26 - ancestorClock size) ancestors := by
  dsimp only
  have tail (entry : WordState bits) (first cut : Nat) (hle : first ≤ cut) :
      packingRun rom containing cut entry =
        packingRun rom containing (cut - first) (packingRun rom containing first entry) := by
    conv_lhs => rw [show cut = first + (cut - first) by omega]
    exact run_add rom containing first (cut - first) entry
  split_ifs with h0 h1 h2 h3
  · rfl
  · exact tail state 86 count (by omega)
  · rw [tail state 86 count (by omega), tail _ (5 + 98 * size) (count - 86) (by omega)]
  · rw [tail state 86 count (by omega), tail _ (5 + 98 * size) (count - 86) (by omega),
      tail _ 26 (count - 86 - (5 + 98 * size)) (by omega)]
  · rw [tail state 86 count (by omega), tail _ (5 + 98 * size) (count - 86) (by omega),
      tail _ 26 (count - 86 - (5 + 98 * size)) (by omega),
      tail _ (ancestorClock size) (count - 86 - (5 + 98 * size) - 26) (by omega)]
end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
