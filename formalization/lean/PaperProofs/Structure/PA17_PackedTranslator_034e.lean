module

public import PaperProofs.Structure.PA17_PackedTranslator_034c
public import PaperProofs.Structure.PA17_PackedTranslator_034d

/-! Real allocated accesses of readMacro32. The incoming index heap remains
arbitrary. Only the saved logical pointer's original heap address bound and
the actual static packed allocation/word extent are used. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM

theorem capAddress_address_le {bits : Nat} (capWords spillBase : Nat) (pointer : Register)
    (rom : PhysicalROM) (state : WordState bits) (hcap : Fits bits capWords) :
    ((executeOps rom (capAddress capWords spillBase pointer) state).register .address).toNat ≤ capWords := by
  rw [capAddress_address _ _ _ _ _ hcap]
  split_ifs with ha
  · exact ha.le
  · simp

theorem scalar_access_bounds {bits : Nat} (q capWords indexWords spillBase heapWords : Nat)
    (hbits : 0 < bits) (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (halloc : spillBase + spillWords ≤ heapWords) (hfoot : Fits bits heapWords)
    (hregion : Fits bits (capWords * CapacityBits.width q)) (state : WordState bits)
    (haddress : (state.register .address).toNat ≤ capWords) :
    Fits bits ((state.register .address).toNat * CapacityBits.width q) ∧
      Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1) ∧
      (state.register .address).toNat * CapacityBits.width q / bits + 1 < heapWords := by
  have hm := Nat.mul_le_mul_right (CapacityBits.width q) haddress
  have hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q) := hm.trans_lt hregion
  have hpacked := packedCapacityWords_mul_bits q capWords hbits
  have hd := Nat.div_le_div_right (c := bits) (hm.trans hpacked)
  rw [Nat.mul_div_cancel _ hbits] at hd
  have hlook : (state.register .address).toNat * CapacityBits.width q / bits + 1 < heapWords := by
    simp only [spillWords] at halloc
    omega
  exact ⟨hstart, hlook.trans hfoot, hlook⟩

theorem readMacro_accessSafe {bits : Nat} (q capWords indexWords spillBase heapWords : Nat)
    (target pointer : Register) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits) (hcap : Fits bits capWords)
    (hregion : Fits bits (capWords * CapacityBits.width q))
    (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (halloc : spillBase + spillWords ≤ heapWords) (hfoot : Fits bits heapWords)
    (haddress : (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat < capWords + indexWords) :
    PackedAccessSafe heapWords rom (readMacro q bits capWords spillBase target pointer) state := by
  let prepared := executeOps rom (capAddress capWords spillBase pointer) state
  let scalar := executeOps rom (readProgram q bits) prepared
  let indexed := executeOps rom (indexAddress q bits capWords spillBase pointer) scalar
  let chosen := executeOps rom [.base (.base (.loadHeap .fresh .index)),
    .base (.base (.select .value .flag .value .fresh))] indexed
  have hptrAccess : spillBase + pointer.word < heapWords := by have := register_word_lt pointer; omega
  have htargetAccess : spillBase + target.word < heapWords := by have := register_word_lt target; omega
  have h1 := capAddress_accessSafe heapWords capWords spillBase pointer rom state (hptrAccess.trans hfoot) hptrAccess
  have hb := scalar_access_bounds q capWords indexWords spillBase heapWords (by omega) hbase halloc hfoot hregion prepared
    (capAddress_address_le capWords spillBase pointer rom state hcap)
  have h2 := readProgram_accessSafe q heapWords rom prepared (by omega) hwidth hb.1 hb.2.1 hb.2.2
  have h3 := indexAddress_accessSafe heapWords q capWords spillBase pointer rom scalar (hptrAccess.trans hfoot) hptrAccess
  have hsHeap : scalar.heap = state.heap := by dsimp only [scalar, prepared]; rw [readProgram_heap, capAddress_heap]
  have hindexAccess : packedCapacityWords q capWords bits +
      ((state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat - capWords) < heapWords := by
    simp only [spillWords] at halloc
    omega
  have hiIndex : (indexed.register .index).toNat = packedCapacityWords q capWords bits +
      ((state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat - capWords) := by
    dsimp only [indexed]
    rw [indexAddress_index _ _ _ _ _ _ hcap, hsHeap, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hindexAccess.trans hfoot)]
  have h4 : PackedAccessSafe heapWords rom [.base (.base (.loadHeap .fresh .index)),
      .base (.base (.select .value .flag .value .fresh))] indexed := by
    intro count hc
    change count < 2 at hc
    interval_cases count <;> simp [executeOps, packingAccessFits, AccessFits, hiIndex, hindexAccess]
  have h5 := saveReg_accessSafe heapWords spillBase target rom chosen (htargetAccess.trans hfoot) htargetAccess
  simp only [readMacro, List.append_assoc]
  exact PackedAccessSafe.append _ _ _ _ _ h1
    (PackedAccessSafe.append _ _ _ _ _ h2
      (PackedAccessSafe.append _ _ _ _ _ h3 (PackedAccessSafe.append _ _ _ _ _ h4 h5)))

end PaperProofs.Structure.LaminarTree.PA17PackedTranslator034
