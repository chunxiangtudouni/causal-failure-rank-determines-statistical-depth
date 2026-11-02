module

public import Structure.PSTR_BuildLower_ConcreteHeap_028

/-! Physical point frames for EVERY actual writer prefix, including the
temporary clear/fill phases. The real72 instructions reload the pointer in
both phases; the existing66-step model is used only through its proved heap
simulation at the corresponding actual prefix. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.PackedPointFrame
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PA06A19PrepareRuntimePacked016
variable {bits : Nat}

theorem prefix_frame (q C slot : Nat) (physical : PhysicalROM) (state : WordState bits)
    (header : Header q state.heap) (hq : 0 < q) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (ha : (PA06A19PrepareBankPacked021.pointer slot state).toNat < C)
    (hs : Fits bits ((PA06A19PrepareBankPacked021.pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((PA06A19PrepareBankPacked021.pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot))
    (point : Nat) (hpoint : Fits bits point)
    (habove : (PA06A19PrepareBankPacked021.pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1 < point)
    (count : Nat) (hc : count ≤ 72) :
    (executeOps physical ((PA06A19PrepareBankPacked021.safeWrite slot).take count) state).heap (BitVec.ofNat bits point) =
      state.heap (BitVec.ofNat bits point) := by
  let reference := PA06A19PrepareBankPacked021.reference slot physical state
  have referenceHeap : reference.heap = state.heap := rfl
  have referenceAddress : reference.register .address = PA06A19PrepareBankPacked021.pointer slot state := rfl
  rw [PA06A19PrepareBankPacked021.safeWrite_prefix_heap_simulation q C slot physical state header hq hb hw ha hs hf hbank hbankFit count hc]
  have modeled := safeWrite_prefix_heap q physical reference (by rwa [referenceHeap]) hb hw
    (by rwa [referenceAddress]) (by rwa [referenceAddress])
    (PA06A19PrepareBankPacked021.oldCount count) (PA06A19PrepareBankPacked021.oldCount_le count hc)
  rw [modeled]
  have lowNe : BitVec.ofNat bits point ≠ BitVec.ofNat bits
      ((PA06A19PrepareBankPacked021.pointer slot state).toNat * CapacityBits.width q / bits + 4) :=
    word_address_ne hpoint (lt_of_le_of_lt (by omega) hf) (by omega)
  have highNe : BitVec.ofNat bits point ≠ BitVec.ofNat bits
      ((PA06A19PrepareBankPacked021.pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1) :=
    word_address_ne hpoint hf (by omega)
  simp only [referenceAddress, referenceHeap]
  split_ifs
  · rfl
  · simp only [physicalClearLow, Function.update_of_ne lowNe]
  · simp only [physicalClear, Function.update_of_ne highNe, physicalClearLow, Function.update_of_ne lowNe]
  · simp only [physicalFillLow, Function.update_of_ne lowNe, physicalClear,
      Function.update_of_ne highNe, physicalClearLow]
  · simp only [physicalWrite, Function.update_of_ne highNe, Function.update_of_ne lowNe]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.PackedPointFrame
