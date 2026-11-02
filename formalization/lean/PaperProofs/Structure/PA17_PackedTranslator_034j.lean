module

public import PaperProofs.Structure.PA17_PackedTranslator_034i

/-! Actual seven-spill initialization and final restoration. Heap statements
are allocated-address statements; arbitrary old index words are preserved. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM

theorem physicalWipe_take_frame {bits : Nat} (spillBase : Nat) (rom : PhysicalROM)
    (state : WordState bits) (hfit : Fits bits (spillBase + spillWords))
    (count : Nat) (hc : count ≤ (physicalWipe spillBase).length)
    (address : BitVec bits) (hout : address.toNat < spillBase ∨ spillBase + spillWords ≤ address.toNat) :
    (executeOps rom ((physicalWipe spillBase).take count) state).heap address = state.heap address := by
  have hn (index : Nat) (hi : index < 7) : address ≠ BitVec.ofNat bits (spillBase + index) := by
    intro heq
    have hh := congrArg BitVec.toNat heq
    have hf : Fits bits (spillBase + index) := by unfold Fits spillWords at *; omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf] at hh
    unfold spillWords at hout
    omega
  have hnzero : address ≠ BitVec.ofNat bits spillBase := by simpa using hn 0 (by omega)
  change count ≤ 16 at hc
  interval_cases count <;>
    simp [physicalWipe, wipe, spillWords, wipeBlock, List.range_succ, executeOps,
      packingExecuteOp, wordOp, wordInstruction, Function.update_of_ne hnzero,
      Function.update_of_ne (hn 1 (by omega)), Function.update_of_ne (hn 2 (by omega)),
      Function.update_of_ne (hn 3 (by omega)), Function.update_of_ne (hn 4 (by omega)),
      Function.update_of_ne (hn 5 (by omega)), Function.update_of_ne (hn 6 (by omega))]

theorem physicalWipe_zero {bits : Nat} (spillBase : Nat) (rom : PhysicalROM)
    (state : WordState bits) (hfit : Fits bits (spillBase + spillWords))
    (index : Nat) (hi : index < spillWords) :
    (executeOps rom (physicalWipe spillBase) state).heap (BitVec.ofNat bits (spillBase + index)) = BitVec.ofNat bits 0 := by
  have hn (i j : Nat) (hi : i < 7) (hj : j < 7) (hne : i ≠ j) :
      BitVec.ofNat bits (spillBase + i) ≠ BitVec.ofNat bits (spillBase + j) := by
    apply (ofNat_injective_of_fit _ _ (by unfold Fits spillWords at *; omega) (by unfold Fits spillWords at *; omega)).not.mpr
    omega
  change index < 7 at hi
  interval_cases index <;>
    simp [physicalWipe, wipe, spillWords, wipeBlock, List.range_succ, executeOps,
      packingExecuteOp, wordOp, wordInstruction, Function.update_apply, hn]

theorem physicalWipe_accessSafe {bits : Nat} (spillBase heapWords : Nat) (rom : PhysicalROM)
    (state : WordState bits) (halloc : spillBase + spillWords ≤ heapWords) (hfit : Fits bits heapWords) :
    PackedAccessSafe heapWords rom (physicalWipe spillBase) state := by
  have hf (index : Nat) (hi : index < 7) : (spillBase + index) % 2 ^ bits < heapWords := by
    rw [Nat.mod_eq_of_lt (show Fits bits (spillBase + index) from by unfold Fits spillWords at *; omega)]
    unfold spillWords at halloc
    omega
  intro count hc
  change count < 16 at hc
  interval_cases count <;>
    simp [physicalWipe, wipe, spillWords, wipeBlock, List.range_succ, executeOps,
      packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits]
  all_goals first
    | simpa using hf 0 (by omega)
    | exact hf 1 (by omega)
    | exact hf 2 (by omega)
    | exact hf 3 (by omega)
    | exact hf 4 (by omega)
    | exact hf 5 (by omega)
    | exact hf 6 (by omega)

theorem physicalWipe_take_old_heap {bits : Nat} (q capWords indexWords spillBase : Nat)
    (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits)
    (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (hfit : Fits bits (spillBase + spillWords)) (hregion : Fits bits (capWords * CapacityBits.width q))
    (count : Nat) (hc : count ≤ (physicalWipe spillBase).length) (address : Nat) (ha : address < capWords + indexWords) :
    unpackHeap q capWords bits (executeOps rom ((physicalWipe spillBase).take count) state).heap address =
      unpackHeap q capWords bits state.heap address := by
  by_cases hcap : address < capWords
  · rw [unpackHeap, unpackHeap, ite_eq_left hcap, ite_eq_left hcap]
    congr 1
    apply congrArg List.ofFn
    funext position
    dsimp only
    have hm := Nat.mul_le_mul_right (CapacityBits.width q) (show address + 1 ≤ capWords by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    have hoff : address * CapacityBits.width q + position.val < capWords * CapacityBits.width q := by
      have := position.isLt
      omega
    have hw : (address * CapacityBits.width q + position.val) / bits < packedCapacityWords q capWords bits := by
      apply (Nat.div_lt_iff_lt_mul hbits).mpr
      exact hoff.trans_le (packedCapacityWords_mul_bits q capWords hbits)
    have hf : Fits bits ((address * CapacityBits.width q + position.val) / bits) :=
      (Nat.div_le_self _ _).trans_lt (hoff.trans hregion)
    rw [physicalWipe_take_frame spillBase rom state hfit count hc _ (Or.inl (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
      omega))]
  · rw [unpackHeap, unpackHeap, ite_eq_right hcap, ite_eq_right hcap]
    have hw : packedCapacityWords q capWords bits + (address - capWords) < spillBase := by omega
    have hf : Fits bits (packedCapacityWords q capWords bits + (address - capWords)) := by
      unfold Fits at *
      omega
    rw [physicalWipe_take_frame spillBase rom state hfit count hc _ (Or.inl (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
      exact hw))]

theorem physicalWipe_decoded_zero {bits : Nat} (q capWords indexWords spillBase : Nat)
    (rom : PhysicalROM) (state : WordState bits)
    (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (hfit : Fits bits (spillBase + spillWords)) (index : Nat) (hi : index < spillWords) :
    unpackHeap q capWords bits (executeOps rom (physicalWipe spillBase) state).heap
      (capWords + indexWords + index) = 0 := by
  rw [unpackHeap, ite_eq_right (show ¬capWords + indexWords + index < capWords by omega)]
  have he : packedCapacityWords q capWords bits + (capWords + indexWords + index - capWords) = spillBase + index := by omega
  rw [he, physicalWipe_zero spillBase rom state hfit index hi]
  simp

theorem physicalWipe_capacitySafe {bits : Nat} (q capWords indexWords spillBase : Nat)
    (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits)
    (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (hfit : Fits bits (spillBase + spillWords)) (hregion : Fits bits (capWords * CapacityBits.width q))
    (hbound : CapacityPrefixBounded q capWords (unpackHeap q capWords bits state.heap)) :
    PA17PackedStore042b.CapacitySafe q capWords rom (physicalWipe spillBase) state := by
  intro count hc address ha
  rw [physicalWipe_take_old_heap q capWords indexWords spillBase rom state hbits hbase hfit hregion count hc address (by omega)]
  exact hbound address ha

theorem physicalWipe_initial_sim {bits : Nat} (q capWords indexWords spillBase : Nat)
    (rom : PhysicalROM) (heap : BitVec bits → BitVec bits) (hbits : 0 < bits)
    (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (hfit : Fits bits (spillBase + spillWords)) (hregion : Fits bits (capWords * CapacityBits.width q)) :
    SpillSim q capWords indexWords spillBase
      (execute rom.semantic (wipe (capWords + indexWords)) (initial (unpackHeap q capWords bits heap)))
      (executeOps rom (physicalWipe spillBase) (packingInitial heap)) := by
  constructor
  · intro register
    change ((executeOps rom (physicalWipe spillBase) (packingInitial heap)).heap
      (BitVec.ofNat bits (spillBase + register.word))).toNat = _
    rw [physicalWipe_zero spillBase rom _ hfit register.word (register_word_lt register), wipe_register]
    cases register <;> rfl
  · intro address ha
    have hp := physicalWipe_take_old_heap q capWords indexWords spillBase rom (packingInitial heap)
      hbits hbase hfit hregion (physicalWipe spillBase).length le_rfl address ha
    rw [List.take_length] at hp
    rw [hp, wipe_frame rom.semantic (capWords + indexWords) _ address (Or.inl ha)]
    rfl

end PaperProofs.Structure.LaminarTree.PA17PackedTranslator034
