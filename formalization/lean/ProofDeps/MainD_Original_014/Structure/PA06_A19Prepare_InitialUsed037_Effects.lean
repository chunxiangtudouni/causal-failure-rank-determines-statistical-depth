module

public import Structure.PA06_A19Prepare_InitialUsed037_Bounds
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate scalar effects of the actual used-loop body. All storage
effects below come from037's actual88-op body_heap, not an assumed writer. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PSTRBuildLower
open AlgorithmClaims.PackedCapacityRAM

variable {bits : Nat}

theorem physicalWrite_bank_frame (q C a physical : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hq : 0 < q) (hb : 0 < bits) (ha : a < C)
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ physical)
    (hbankFit : Fits bits physical) (hnext : Fits bits (a * CapacityBits.width q / bits + 4 + 1)) :
    PA06A19PrepareRuntimePacked016.physicalWrite (CapacityBits.width q) (a * CapacityBits.width q) value heap
      (BitVec.ofNat bits physical) = heap (BitVec.ofNat bits physical) := by
  have hd : a * CapacityBits.width q / bits < packedCapacityWords q C bits := by
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    exact (Nat.mul_lt_mul_of_pos_right ha (PA17PackedTemplates046.width_pos q hq)).trans_le
      (packedCapacityWords_mul_bits q C hb)
  have hbefore : a * CapacityBits.width q / bits + 4 + 1 < physical := by omega
  have hlo : Fits bits (a * CapacityBits.width q / bits + 4) := (Nat.le_succ _).trans_lt hnext
  have hneHigh : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (a * CapacityBits.width q / bits + 4 + 1) :=
    (ofNat_injective_of_fit _ _ hbankFit hnext).not.mpr (Nat.ne_of_gt hbefore)
  have hneLow : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (a * CapacityBits.width q / bits + 4) :=
    (ofNat_injective_of_fit _ _ hbankFit hlo).not.mpr (by omega)
  simp only [PA06A19PrepareRuntimePacked016.physicalWrite, Function.update_of_ne hneHigh,
    Function.update_of_ne hneLow]

theorem update_control_capacity (q C physical : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hb : 0 < bits) (hregion : Fits bits (C * CapacityBits.width q))
    (hafter : 4 + packedCapacityWords q C bits ≤ physical) (hfit : Fits bits physical)
    (other : Nat) (ho : other < C) :
    unpackHeap q C bits (dataHeap (Function.update heap (BitVec.ofNat bits physical) value)) other =
      unpackHeap q C bits (dataHeap heap) other := by
  have hh := PA06A19PreparePackedView013.indexStore_capacity_frame q 0 C physical 0 value heap hb hregion hafter
    (by simpa only [Nat.sub_self, Nat.add_zero] using hfit) other ho
  simpa only [PA06A19PreparePackedView013.indexStore, Nat.sub_self, Nat.add_zero] using hh

theorem increment_toNat (value : BitVec bits) (hnext : Fits bits (value.toNat + 1)) :
    (value + BitVec.ofNat bits 1).toNat = value.toNat + 1 := by
  have hone : Fits bits 1 := (by omega : 1 ≤ value.toNat + 1).trans_lt hnext
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt hnext]

theorem body_controls (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (ha : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat < C)
    (hs : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + pointerSlot)
    (hfit16 : Fits bits ((state.register .address).toNat + pointerSlot))
    (hfit17 : Fits bits ((state.register .address).toNat + cursorSlot))
    (hfit18 : Fits bits ((state.register .address).toNat + counterSlot)) :
    let after := executeOps rom body state
    after.heap (state.register .address + BitVec.ofNat bits pointerSlot) =
        state.heap (state.register .address + BitVec.ofNat bits pointerSlot) + BitVec.ofNat bits 1 ∧
      after.heap (state.register .address + BitVec.ofNat bits cursorSlot) =
        state.heap (state.register .address + BitVec.ofNat bits cursorSlot) + BitVec.ofNat bits 1 ∧
      after.heap (state.register .address + BitVec.ofNat bits counterSlot) =
        state.heap (state.register .address + BitVec.ofNat bits counterSlot) := by
  let CB := (state.register .address).toNat
  let a := (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat
  let value := BitVec.ofNat bits (rom.semantic.read .input
    (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat)
  let written := PA06A19PrepareRuntimePacked016.physicalWrite (CapacityBits.width q) (a * CapacityBits.width q) value state.heap
  have hwrite16 : written (BitVec.ofNat bits (CB + pointerSlot)) = state.heap (BitVec.ofNat bits (CB + pointerSlot)) :=
    physicalWrite_bank_frame q C a (CB + pointerSlot) value state.heap hq hb ha hbank hfit16 hf
  have hwrite17 : written (BitVec.ofNat bits (CB + cursorSlot)) = state.heap (BitVec.ofNat bits (CB + cursorSlot)) :=
    physicalWrite_bank_frame q C a (CB + cursorSlot) value state.heap hq hb ha
      (by dsimp only [pointerSlot, cursorSlot] at *; omega) hfit17 hf
  have hwrite18 : written (BitVec.ofNat bits (CB + counterSlot)) = state.heap (BitVec.ofNat bits (CB + counterSlot)) :=
    physicalWrite_bank_frame q C a (CB + counterSlot) value state.heap hq hb ha
      (by dsimp only [pointerSlot, counterSlot] at *; omega) hfit18 hf
  have hne16_17 : BitVec.ofNat bits (CB + pointerSlot) ≠ BitVec.ofNat bits (CB + cursorSlot) :=
    (ofNat_injective_of_fit _ _ hfit16 hfit17).not.mpr (by dsimp only [pointerSlot, cursorSlot]; omega)
  have hne18_16 : BitVec.ofNat bits (CB + counterSlot) ≠ BitVec.ofNat bits (CB + pointerSlot) :=
    (ofNat_injective_of_fit _ _ hfit18 hfit16).not.mpr (by dsimp only [counterSlot, pointerSlot]; omega)
  have hne18_17 : BitVec.ofNat bits (CB + counterSlot) ≠ BitVec.ofNat bits (CB + cursorSlot) :=
    (ofNat_injective_of_fit _ _ hfit18 hfit17).not.mpr (by dsimp only [counterSlot, cursorSlot]; omega)
  have hheap : (executeOps rom body state).heap = Function.update
      (Function.update written (BitVec.ofNat bits (CB + pointerSlot))
        (written (BitVec.ofNat bits (CB + pointerSlot)) + BitVec.ofNat bits 1))
      (BitVec.ofNat bits (CB + cursorSlot))
      ((Function.update written (BitVec.ofNat bits (CB + pointerSlot))
        (written (BitVec.ofNat bits (CB + pointerSlot)) + BitVec.ofNat bits 1))
          (BitVec.ofNat bits (CB + cursorSlot)) + BitVec.ofNat bits 1) := by
    rw [body_heap q C rom state hh hq hb hw ha hs hf hbank hfit16]
    change Function.update
      (Function.update written (state.register .address + BitVec.ofNat bits pointerSlot)
        (written (state.register .address + BitVec.ofNat bits pointerSlot) + BitVec.ofNat bits 1))
      (state.register .address + BitVec.ofNat bits cursorSlot)
      ((Function.update written (state.register .address + BitVec.ofNat bits pointerSlot)
        (written (state.register .address + BitVec.ofNat bits pointerSlot) + BitVec.ofNat bits 1))
          (state.register .address + BitVec.ofNat bits cursorSlot) + BitVec.ofNat bits 1) = _
    simp only [CB, PA06A19PrepareBankPacked021.bankWord_eq]
  dsimp only [CB] at hheap hwrite16 hwrite17 hwrite18 hne16_17 hne18_16 hne18_17
  dsimp only
  simp only [hheap, PA06A19PrepareBankPacked021.bankWord_eq, Function.update_self,
    Function.update_of_ne hne16_17, Function.update_of_ne (Ne.symm hne16_17),
    Function.update_of_ne hne18_16, Function.update_of_ne hne18_17, hwrite16, hwrite17, hwrite18]
  exact ⟨True.intro, True.intro, True.intro⟩

theorem body_target (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (ha : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat < C)
    (hs : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + pointerSlot)
    (hfit16 : Fits bits ((state.register .address).toNat + pointerSlot))
    (hfit17 : Fits bits ((state.register .address).toNat + cursorSlot))
    (hregion : Fits bits (C * CapacityBits.width q))
    (hv : (BitVec.ofNat bits (rom.semantic.read .input
      (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat)).toNat ≤ q) :
    unpackHeap q C bits (dataHeap (executeOps rom body state).heap)
      (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat =
      (BitVec.ofNat bits (rom.semantic.read .input
        (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat)).toNat := by
  have hafter16 : 4 + packedCapacityWords q C bits ≤ (state.register .address).toNat + pointerSlot := by omega
  have hafter17 : 4 + packedCapacityWords q C bits ≤ (state.register .address).toNat + cursorSlot := by
    dsimp only [pointerSlot, cursorSlot] at *
    omega
  rw [body_heap q C rom state hh hq hb hw ha hs hf hbank hfit16, bodyHeap]
  simp only [PA06A19PrepareBankPacked021.bankWord_eq]
  rw [update_control_capacity q C ((state.register .address).toNat + cursorSlot) _ _ hb hregion hafter17 hfit17 _ ha,
    update_control_capacity q C ((state.register .address).toNat + pointerSlot) _ _ hb hregion hafter16 hfit16 _ ha,
    PA06A19PrepareRuntimePacked016.dataHeap_physicalWrite]
  exact unpackHeap_write_target q C _ _ (dataHeap state.heap) hb hw ha
    ((by omega : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 1 ≤
      (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1).trans_lt hf)
    (by simpa only [PA06A19PrepareBankPacked021.bankWord_eq] using CapacityBits.value_lt_two_pow_width q _ hv)

theorem body_other_capacity (q C other : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (ha : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat < C)
    (hs : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + pointerSlot)
    (hfit16 : Fits bits ((state.register .address).toNat + pointerSlot))
    (hfit17 : Fits bits ((state.register .address).toNat + cursorSlot))
    (hregion : Fits bits (C * CapacityBits.width q))
    (hv : (BitVec.ofNat bits (rom.semantic.read .input
      (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat)).toNat ≤ q)
    (ho : other < C) (hne : other ≠ (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat) :
    unpackHeap q C bits (dataHeap (executeOps rom body state).heap) other = unpackHeap q C bits (dataHeap state.heap) other := by
  have hafter16 : 4 + packedCapacityWords q C bits ≤ (state.register .address).toNat + pointerSlot := by omega
  have hafter17 : 4 + packedCapacityWords q C bits ≤ (state.register .address).toNat + cursorSlot := by
    dsimp only [pointerSlot, cursorSlot] at *
    omega
  rw [body_heap q C rom state hh hq hb hw ha hs hf hbank hfit16, bodyHeap]
  simp only [PA06A19PrepareBankPacked021.bankWord_eq]
  rw [update_control_capacity q C ((state.register .address).toNat + cursorSlot) _ _ hb hregion hafter17 hfit17 other ho,
    update_control_capacity q C ((state.register .address).toNat + pointerSlot) _ _ hb hregion hafter16 hfit16 other ho,
    PA06A19PrepareRuntimePacked016.dataHeap_physicalWrite]
  exact unpackHeap_write_other_capacity q C _ other _ (dataHeap state.heap) hb hw
    ((by omega : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 1 ≤
      (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1).trans_lt hf)
    hregion (by simpa only [PA06A19PrepareBankPacked021.bankWord_eq] using CapacityBits.value_lt_two_pow_width q _ hv) ho hne

theorem physicalWrite_ordinary_frame (q C a : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits) (ha : a < C)
    (hnext : Fits bits (a * CapacityBits.width q / bits + 1))
    (hv : value.toNat < 2 ^ CapacityBits.width q)
    (point : BitVec bits) (hpoint : 4 + packedCapacityWords q C bits ≤ point.toNat) :
    PA06A19PrepareRuntimePacked016.physicalWrite (CapacityBits.width q) (a * CapacityBits.width q) value heap point = heap point := by
  let P := packedCapacityWords q C bits
  let other := C + (point.toNat - (4 + P))
  have ho : C ≤ other := by dsimp only [other]; omega
  have hindex : P + (other - C) = point.toNat - 4 := by dsimp only [other]; omega
  have hindexFit : Fits bits (P + (other - C)) := by
    rw [hindex]
    exact (Nat.sub_le _ _).trans_lt point.isLt
  have he := unpackHeap_write_index q C a other value (dataHeap heap) hb hw ha ho hnext hindexFit hv
  rw [← PA06A19PrepareRuntimePacked016.dataHeap_physicalWrite (CapacityBits.width q)
    (a * CapacityBits.width q) value heap] at he
  have hword : BitVec.ofNat bits (4 + (P + (other - C))) = point := by
    rw [show 4 + (P + (other - C)) = point.toNat by omega, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hnot : ¬ other < C := by omega
  dsimp only [P] at hword
  simp only [unpackHeap, hnot, ite_false, PA06A19PreparePackedView013.dataHeap_word, hword] at he
  exact BitVec.eq_of_toNat_eq he

/-- Metadata, permanent bank fields and high raw cache are framed. Only
the two actual body-owned cursor cells are excluded here; the real loop
tail separately writes its third owned remaining cell. -/
theorem body_ordinary_frame (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (ha : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat < C)
    (hs : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + pointerSlot)
    (hfit16 : Fits bits ((state.register .address).toNat + pointerSlot))
    (hv : (BitVec.ofNat bits (rom.semantic.read .input
      (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat)).toNat ≤ q)
    (point : BitVec bits) (hpoint : 4 + packedCapacityWords q C bits ≤ point.toNat)
    (hne16 : point ≠ state.register .address + BitVec.ofNat bits pointerSlot)
    (hne17 : point ≠ state.register .address + BitVec.ofNat bits cursorSlot) :
    (executeOps rom body state).heap point = state.heap point := by
  rw [body_heap q C rom state hh hq hb hw ha hs hf hbank hfit16, bodyHeap]
  simp only [Function.update_of_ne hne17, Function.update_of_ne hne16]
  exact physicalWrite_ordinary_frame q C _ _ state.heap hb hw ha
    ((by omega : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 1 ≤
      (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1).trans_lt hf)
    (CapacityBits.value_lt_two_pow_width q _ hv) point hpoint

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037
