module

public import PaperProofs.Structure.PA17_PackedTranslator_034b

/-! Actual packed heap-load macro: its two physical paths are both executed,
the runtime comparison selects the original logical word, and its sole write
is the selected virtual-register spill. No index-heap value bound is assumed. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM

theorem readMacro_value_expr {bits : Nat} (q capWords spillBase : Nat) (target pointer : Register)
    (rom : PhysicalROM) (state : WordState bits) (hcap : Fits bits capWords) :
    (executeOps rom (readMacro q bits capWords spillBase target pointer) state).register .value =
      if (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat < capWords then
        (executeOps rom (readProgram q bits) (executeOps rom (capAddress capWords spillBase pointer) state)).register .value else
        state.heap (BitVec.ofNat bits (packedCapacityWords q capWords bits +
          ((state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat - capWords))) := by
  let scalar := executeOps rom (readProgram q bits) (executeOps rom (capAddress capWords spillBase pointer) state)
  let indexed := executeOps rom (indexAddress q bits capWords spillBase pointer) scalar
  let chosen := executeOps rom [.base (.base (.loadHeap .fresh .index)),
    .base (.base (.select .value .flag .value .fresh))] indexed
  have hwhole : executeOps rom (readMacro q bits capWords spillBase target pointer) state =
      executeOps rom (saveReg spillBase target) chosen := by
    simp only [readMacro, executeOps_append]
    rfl
  have hsHeap : scalar.heap = state.heap := by dsimp only [scalar]; rw [readProgram_heap, capAddress_heap]
  have hsFlag : scalar.register .flag =
      BitVec.ofNat bits (capWords - (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat) := by
    dsimp only [scalar]
    rw [readProgram_flag, capAddress_flag _ _ _ _ _ hcap]
  have hiHeap : indexed.heap = state.heap := (indexAddress_heap q capWords spillBase pointer rom scalar).trans hsHeap
  have hiIndex : indexed.register .index = BitVec.ofNat bits (packedCapacityWords q capWords bits +
      ((state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat - capWords)) := by
    dsimp only [indexed]
    rw [indexAddress_index _ _ _ _ _ _ hcap, hsHeap]
  have hiFlag : indexed.register .flag = scalar.register .flag := indexAddress_flag q capWords spillBase pointer rom scalar
  have hiValue : indexed.register .value = scalar.register .value := indexAddress_value q capWords spillBase pointer rom scalar
  rw [hwhole, saveReg_register_frame spillBase target rom chosen .value (by decide)]
  change (if (indexed.register .flag).toNat = 0 then indexed.heap (indexed.register .index) else indexed.register .value) = _
  rw [hiIndex, hiHeap, hiFlag, hiValue, hsFlag]
  have hsub : capWords - (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat < 2 ^ bits :=
    (Nat.sub_le _ _).trans_lt hcap
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsub]
  by_cases ha : (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat < capWords
  · have hz : capWords - (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat ≠ 0 := by omega
    simp only [ha, hz, ite_false, ite_true]
    rfl
  · have hz : capWords - (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat = 0 := by omega
    simp only [ha, hz, ite_true, ite_false]

theorem readMacro_value {bits : Nat} (q capWords spillBase : Nat) (target pointer : Register)
    (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits)
    (hwidth : CapacityBits.width q ≤ bits) (hcap : Fits bits capWords)
    (hregion : Fits bits (capWords * CapacityBits.width q)) :
    ((executeOps rom (readMacro q bits capWords spillBase target pointer) state).register .value).toNat =
      unpackHeap q capWords bits state.heap (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat := by
  rw [readMacro_value_expr q capWords spillBase target pointer rom state hcap]
  by_cases ha : (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat < capWords
  · simp only [ha, ite_true]
    let prepared := executeOps rom (capAddress capWords spillBase pointer) state
    have hadr : prepared.register .address = state.heap (BitVec.ofNat bits (spillBase + pointer.word)) := by
      dsimp only [prepared]
      rw [capAddress_address _ _ _ _ _ hcap, ite_eq_left ha]
    have hstart : Fits bits ((prepared.register .address).toNat * CapacityBits.width q) := by
      rw [hadr]
      exact (Nat.mul_le_mul_right (CapacityBits.width q) ha.le).trans_lt hregion
    have hread := readProgram_value q rom prepared hbits hwidth hstart
    change ((executeOps rom (readProgram q bits) prepared).register .value).toNat = _
    rw [hread, hadr, show prepared.heap = state.heap from capAddress_heap capWords spillBase pointer rom state]
    exact readTwoWords_eq_unpackHeap q capWords _ state.heap hbits hwidth ha
  · simp only [ha, ite_false, unpackHeap]

theorem readMacro_heap {bits : Nat} (q capWords spillBase : Nat) (target pointer : Register)
    (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (readMacro q bits capWords spillBase target pointer) state).heap =
      Function.update state.heap (BitVec.ofNat bits (spillBase + target.word))
        ((executeOps rom (readMacro q bits capWords spillBase target pointer) state).register .value) := by
  let chosen := executeOps rom [.base (.base (.loadHeap .fresh .index)), .base (.base (.select .value .flag .value .fresh))]
    (executeOps rom (indexAddress q bits capWords spillBase pointer)
      (executeOps rom (readProgram q bits) (executeOps rom (capAddress capWords spillBase pointer) state)))
  have hwhole : executeOps rom (readMacro q bits capWords spillBase target pointer) state =
      executeOps rom (saveReg spillBase target) chosen := by
    simp only [readMacro, executeOps_append]
    rfl
  rw [hwhole, saveReg_heap, saveReg_register_frame spillBase target rom chosen .value (by decide)]
  rfl

theorem readMacro_take_heap {bits : Nat} (q capWords spillBase : Nat) (target pointer : Register)
    (rom : PhysicalROM) (state : WordState bits) (count : Nat)
    (hc : count ≤ (readMacro q bits capWords spillBase target pointer).length) :
    (executeOps rom ((readMacro q bits capWords spillBase target pointer).take count) state).heap =
      if count < 32 then state.heap else (executeOps rom (readMacro q bits capWords spillBase target pointer) state).heap := by
  change count ≤ 32 at hc
  by_cases hk : count < 32
  · rw [ite_eq_left hk]
    interval_cases count <;> rfl
  · have heq : count = 32 := by omega
    subst count
    rw [show 32 = (readMacro q bits capWords spillBase target pointer).length from rfl, List.take_length]
    rfl

theorem readMacro_prefix_capacity_frame {bits : Nat} (q capWords spillBase : Nat) (target pointer : Register)
    (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits)
    (hregion : Fits bits (capWords * CapacityBits.width q))
    (hspill : packedCapacityWords q capWords bits ≤ spillBase) (hphysical : Fits bits (spillBase + target.word))
    (count : Nat) (hc : count ≤ (readMacro q bits capWords spillBase target pointer).length)
    (address : Nat) (ha : address < capWords) :
    unpackHeap q capWords bits (executeOps rom ((readMacro q bits capWords spillBase target pointer).take count) state).heap address =
      unpackHeap q capWords bits state.heap address := by
  rw [readMacro_take_heap q capWords spillBase target pointer rom state count hc]
  split_ifs
  · rfl
  · rw [readMacro_heap]
    exact index_update_capacity q capWords (spillBase + target.word) _ state.heap hbits hregion (by omega) hphysical address ha

end PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

