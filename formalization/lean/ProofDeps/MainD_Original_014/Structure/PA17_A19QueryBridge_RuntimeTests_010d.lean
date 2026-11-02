module

public import Structure.PA17_A19QueryBridge_RuntimeTests_010a

/-! Every prefix of the actual three-op header store preserves the leading
physical heap, including all headers, packed capacities, metadata, used bits,
counts, sentinel parents and H0..H7. Scalar read addresses are derived from
the represented row extent, also for unrestricted VOID payloads. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM

theorem loadSlot_prefix_heap {bits : Nat} (rom : PhysicalROM) (offset : Nat)
    (target : Register) (state : WordState bits) (count : Nat) :
    (executeOps rom ((loadSlot offset target).take count) state).heap = state.heap := by
  apply executeOps_heap_of_no_store
  intro op ho
  exact loadSlot_noStore offset target op (List.mem_of_mem_take ho)

theorem storeSlot_prefix_frame {bits : Nat} (rom : PhysicalROM) (offset header : Nat)
    (source : Register) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (header + offset))
    (count : Nat) (hc : count ≤ 3) :
    (executeOps rom ((storeSlot offset source).take count) state).heap address = state.heap address := by
  interval_cases count <;>
    simp +decide [storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hh, BitVec.ofNat_add_ofNat, Function.update_of_ne hne]

theorem storeSlot_prefix_header {bits : Nat} (rom : PhysicalROM) (offset : Nat)
    (source : Register) (state : WordState bits) (count : Nat) (hc : count ≤ 3) :
    (executeOps rom ((storeSlot offset source).take count) state).register .address = state.register .address := by
  interval_cases count <;>
    simp +decide [storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem storeSlot_prefix_leading_frame {bits : Nat} (rom : PhysicalROM) (offset header : Nat)
    (source : Register) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hroom : Fits bits (header + 16)) (ho : 8 ≤ offset) (hu : offset < 16)
    (physical : Nat) (hp : physical < header + 8) (count : Nat) (hc : count ≤ 3) :
    (executeOps rom ((storeSlot offset source).take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  apply storeSlot_prefix_frame rom offset header source state hh _ ?_ count hc
  intro heq
  have he := (ofNat_injective_of_fit _ _ ((show physical ≤ header + 16 by omega).trans_lt hroom)
    ((show header + offset ≤ header + 16 by omega).trans_lt hroom)).mp heq
  omega

theorem represented_row_scalar_lt (size q rowBase capWords budget nodeOffset : Nat)
    (hrow : rowBase + (q + 2) * (size + 1) ≤ capWords)
    (hb : budget < q + 2) (hn : nodeOffset ≤ size) :
    rowBase + budget * (size + 1) + nodeOffset < capWords := by
  have hm := Nat.mul_le_mul_right (size + 1) (show budget + 1 ≤ q + 2 by omega)
  nlinarith

theorem represented_row_scalar_fit {bits : Nat} (size q rowBase capWords budget nodeOffset : Nat)
    (hrow : rowBase + (q + 2) * (size + 1) ≤ capWords)
    (hb : budget < q + 2) (hn : nodeOffset ≤ size) (hc : Fits bits capWords) :
    Fits bits (rowBase + budget * (size + 1) + nodeOffset) :=
  (represented_row_scalar_lt size q rowBase capWords budget nodeOffset hrow hb hn).trans hc

theorem reverse_node_scalar_lt (size q rowBase capWords budget remaining : Nat)
    (hrow : rowBase + (q + 2) * (size + 1) ≤ capWords)
    (hb : budget < q + 2) (hn : remaining < size) :
    rowBase + budget * (size + 1) + 1 + remaining < capWords := by
  have hh := represented_row_scalar_lt size q rowBase capWords budget (1 + remaining) hrow hb (by omega)
  simpa only [Nat.add_assoc] using hh

theorem ancestor_scalar_lt (size q rowBase capWords budget encoded : Nat)
    (hrow : rowBase + (q + 2) * (size + 1) ≤ capWords)
    (hb : budget < q + 2) (ht : 0 < size) (he : encoded ≤ size) :
    rowBase + budget * (size + 1) + 1 + (encoded - 1) < capWords := by
  have hh := represented_row_scalar_lt size q rowBase capWords budget (1 + (encoded - 1))
    hrow hb (by omega)
  simpa only [Nat.add_assoc] using hh

theorem counts_node_lt_header (workspace size node : Nat) (hn : node < size) :
    PSTRQueryLayout.countsBase workspace + node < PSTRQueryLayout.header workspace size := by
  unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
  omega

theorem counts_encoded_lt_header (workspace size encoded : Nat) (ht : 0 < size) (he : encoded ≤ size) :
    PSTRQueryLayout.countsBase workspace + (encoded - 1) < PSTRQueryLayout.header workspace size := by
  apply counts_node_lt_header
  omega

theorem parent_encoded_lt_header (workspace size encoded : Nat) (he : encoded ≤ size) :
    PSTRQueryLayout.parentsBase workspace size + encoded < PSTRQueryLayout.header workspace size := by
  unfold PSTRQueryLayout.header
  omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
