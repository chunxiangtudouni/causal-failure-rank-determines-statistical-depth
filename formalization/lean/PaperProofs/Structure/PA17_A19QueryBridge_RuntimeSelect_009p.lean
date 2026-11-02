module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009o

/-! Prefix heap-frame composition for the actual Word instruction lists.
The concrete suffix theorem below is derived from runtime source cells,
not from a supplied execution trace or all-prefix frame oracle. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def WordPrefixFrame {bits : Nat} (rom : PhysicalROM) (code : List PackingOp)
    (state : WordState bits) (address : BitVec bits) : Prop :=
  ∀ clock ≤ code.length, (executeOps rom (code.take clock) state).heap address = state.heap address

theorem WordPrefixFrame.noStore {bits : Nat} (rom : PhysicalROM) (code : List PackingOp)
    (state : WordState bits) (address : BitVec bits) (hn : ∀ op ∈ code, HeapPreservingOp op) :
    WordPrefixFrame rom code state address := by
  intro clock _
  exact congrFun (executeOps_heap_of_no_store rom (code.take clock) state
    (by intro op ho; exact hn op (List.mem_of_mem_take ho))) address

theorem WordPrefixFrame.append {bits : Nat} (rom : PhysicalROM) (left right : List PackingOp)
    (state : WordState bits) (address : BitVec bits)
    (hl : WordPrefixFrame rom left state address)
    (hr : WordPrefixFrame rom right (executeOps rom left state) address) :
    WordPrefixFrame rom (left ++ right) state address := by
  intro clock hc
  by_cases hleft : clock ≤ left.length
  · rw [List.take_append_of_le_length hleft]
    exact hl clock hleft
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show left.length ≤ clock by omega)
    have he : extra ≤ right.length := by rw [List.length_append] at hc; omega
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, executeOps_append]
    exact (hr extra he).trans (by simpa only [List.take_length] using hl left.length le_rfl)

theorem reverseFoot_prefixFrame {bits : Nat} (rom : PhysicalROM) (origin header : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (address : BitVec bits)
    (hne : address ≠ BitVec.ofNat bits (header + 8)) : WordPrefixFrame rom (reverseFoot origin) state address := by
  intro clock hc
  change clock ≤ 9 at hc
  interval_cases clock <;>
    simp_all +decide [reverseFoot, reverseFootLead, executeOps, packingExecuteOp, wordOp, wordInstruction,
      BitVec.ofNat_add_ofNat]

theorem pushProgram_prefixFrame_cells {bits : Nat} (rom : PhysicalROM)
    (header candidates counts parents node parent : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hn : Fits bits (node + 1)) (hparent : Fits bits parent)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hcandidates : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits candidates)
    (hcounts : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts)
    (hparents : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents)
    (hreadParent : state.heap (BitVec.ofNat bits (parents + (node + 1))) = BitVec.ofNat bits parent)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (candidates + parent)) :
    WordPrefixFrame rom pushProgram state address := by
  have hv : state.register .value = BitVec.ofNat bits (state.register .value).toNat := by
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hcount : state.heap (BitVec.ofNat bits (counts + node)) =
      BitVec.ofNat bits (state.heap (BitVec.ofNat bits (counts + node))).toNat := by
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  intro clock hc
  apply pushProgram_prefix_frame rom header candidates counts parents node parent
    (state.register .value).toNat (state.heap (BitVec.ofNat bits (counts + node))).toNat state
    h1 hn hparent (BitVec.isLt _) (BitVec.isLt _) hh hv hnode hcandidates hcounts hparents hcount hreadParent
    clock (by simpa only [pushProgram_length] using hc) address hne

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
