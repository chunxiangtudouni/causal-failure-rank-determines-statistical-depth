module
public import PaperProofs.Structure.PA17_PackedTranslator_034b

/-! Real write87 prefix setup. Index values remain arbitrary BitVec words;
only the selected capacity scalar is required to be q-bounded. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
namespace PaperProofs.Structure.LaminarTree.PA17PackedStore042a

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM PA17PackedTranslator034

def saved {bits : Nat} (spill : Nat) (register : Register) (state : WordState bits) : BitVec bits :=
  state.heap (BitVec.ofNat bits (spill + register.word))

def chosenAddress (cap address : Nat) : Nat := if address < cap then address else 0

def selectInput (q bits cap spill : Nat) (pointer source : Register) : List PackingOp :=
  capAddress cap spill pointer ++ readProgram q bits ++ loadReg spill source .fresh ++
    [.base (.base (.select .value .flag .fresh .value))]

theorem selectInput_length (q bits cap spill : Nat) (pointer source : Register) :
    (selectInput q bits cap spill pointer source).length = 25 := rfl

theorem selectInput_heap {bits : Nat} (q cap spill : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (selectInput q bits cap spill pointer source) state).heap = state.heap := by
  rw [selectInput, executeOps_append, executeOps_append, executeOps_append]
  change (executeOps rom (loadReg spill source .fresh)
    (executeOps rom (readProgram q bits) (executeOps rom (capAddress cap spill pointer) state))).heap = state.heap
  rw [loadReg_heap, readProgram_heap, capAddress_heap]

theorem selectInput_address {bits : Nat} (q cap spill : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hcap : Fits bits cap) :
    (executeOps rom (selectInput q bits cap spill pointer source) state).register .address =
      BitVec.ofNat bits (chosenAddress cap (saved spill pointer state).toNat) := by
  rw [selectInput, executeOps_append, executeOps_append, executeOps_append]
  change (executeOps rom (loadReg spill source .fresh)
    (executeOps rom (readProgram q bits) (executeOps rom (capAddress cap spill pointer) state))).register .address = _
  rw [loadReg_register_frame spill source .fresh rom _ .address (by decide) (by decide),
    readProgram_address, capAddress_address _ _ _ _ _ hcap]
  unfold chosenAddress saved
  split_ifs with ha
  · simp
  · rfl

theorem selectInput_value_expr {bits : Nat} (q cap spill : Nat) (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hcap : Fits bits cap) :
    (executeOps rom (selectInput q bits cap spill pointer source) state).register .value =
      if (saved spill pointer state).toNat < cap then saved spill source state else
        (executeOps rom (readProgram q bits) (executeOps rom (capAddress cap spill pointer) state)).register .value := by
  let scalar := executeOps rom (readProgram q bits) (executeOps rom (capAddress cap spill pointer) state)
  have hsheap : scalar.heap = state.heap := by dsimp only [scalar]; rw [readProgram_heap, capAddress_heap]
  have hsflag : scalar.register .flag = BitVec.ofNat bits (cap - (saved spill pointer state).toNat) := by
    dsimp only [scalar]
    rw [readProgram_flag, capAddress_flag _ _ _ _ _ hcap]
    rfl
  rw [selectInput, executeOps_append, executeOps_append, executeOps_append]
  change (if ((executeOps rom (loadReg spill source .fresh) scalar).register .flag).toNat = 0 then
    (executeOps rom (loadReg spill source .fresh) scalar).register .value else
    (executeOps rom (loadReg spill source .fresh) scalar).register .fresh) = _
  rw [loadReg_register_frame spill source .fresh rom scalar .flag (by decide) (by decide),
    loadReg_register_frame spill source .fresh rom scalar .value (by decide) (by decide),
    loadReg_value, hsheap, hsflag]
  have hf : cap - (saved spill pointer state).toNat < 2 ^ bits := (Nat.sub_le _ _).trans_lt hcap
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
  by_cases ha : (saved spill pointer state).toNat < cap
  · have hne : cap - (saved spill pointer state).toNat ≠ 0 := by omega
    simp only [ha, hne, ite_true, ite_false]
    rfl
  · have hz : cap - (saved spill pointer state).toNat = 0 := by omega
    simp only [ha, hz, ite_true, ite_false]
    rfl

theorem chosenAddress_lt (cap address : Nat) (hc : 0 < cap) : chosenAddress cap address < cap := by
  unfold chosenAddress
  split_ifs <;> omega

theorem packed_lookahead_le (q cap bits address : Nat) (hb : 0 < bits) (ha : address < cap) :
    address * CapacityBits.width q / bits + 1 ≤ packedCapacityWords q cap bits + 1 := by
  have hm := Nat.mul_le_mul_right (CapacityBits.width q) ha.le
  have hp := packedCapacityWords_mul_bits q cap hb
  have hh : address * CapacityBits.width q / bits < packedCapacityWords q cap bits + 1 := by
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    rw [Nat.add_mul, Nat.one_mul]
    omega
  omega

theorem selectInput_value (q cap spill : Nat) {bits : Nat} (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hcap : Fits bits cap) (hc : 0 < cap) :
    ((executeOps rom (selectInput q bits cap spill pointer source) state).register .value).toNat =
      if (saved spill pointer state).toNat < cap then (saved spill source state).toNat else unpackHeap q cap bits state.heap 0 := by
  rw [selectInput_value_expr q cap spill pointer source rom state hcap]
  split_ifs with ha
  · rfl
  · let prepared := executeOps rom (capAddress cap spill pointer) state
    have had : prepared.register .address = BitVec.ofNat bits 0 := by
      dsimp only [prepared]
      rw [capAddress_address _ _ _ _ _ hcap]
      simp only [saved] at ha
      simp only [ha, ite_false]
    have hs : Fits bits ((prepared.register .address).toNat * CapacityBits.width q) := by
      rw [had]
      simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul]
      exact pow_pos (by decide) _
    rw [readProgram_value q rom prepared hbits hwidth hs, had]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.zero_add]
    have hu := readTwoWords_eq_unpackHeap q cap 0 prepared.heap hbits hwidth hc
    simp only [Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.zero_add] at hu
    rw [show prepared.heap = state.heap from capAddress_heap cap spill pointer rom state] at hu
    exact hu

theorem selectInput_capacityBound (q cap spill : Nat) {bits : Nat} (pointer source : Register)
    (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hcap : Fits bits cap) (hc : 0 < cap)
    (hsource : (saved spill pointer state).toNat < cap → (saved spill source state).toNat ≤ q)
    (hbound : CapacityPrefixBounded q cap (unpackHeap q cap bits state.heap)) :
    ((executeOps rom (selectInput q bits cap spill pointer source) state).register .value).toNat ≤ q := by
  rw [selectInput_value q cap spill pointer source rom state hbits hwidth hcap hc]
  split_ifs with ha
  · exact hsource ha
  · exact hbound 0 hc

end PaperProofs.Structure.LaminarTree.PA17PackedStore042a
