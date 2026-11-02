module

public import Structure.PSTR_BuildLower_TraceAccess_119
public import Structure.PSTR_BuildLower_RuntimeData_062

/-! Direct Word access for the actual25-op parent/degree getter. The true
produced mass/size and original in-range pointer give the REAL cache target;
the whole heap is readonly at every fetched prefix. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.InternalAccess
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open RawTreePreprocessingClaims PA17PackedTranslator034

section Generic
variable {bits : Nat}

private theorem index_target (physical : PhysicalROM) (pointer : Register) (state : WordState bits) :
    (executeOps physical ((InternalInput.code pointer).take 24) state).register .index =
      InternalInput.targetAddress state pointer := by
  have hd : (state.heap (state.register .address + BitVec.ofNat bits 2)).toNat -
      (Ordinary.pointerValue state pointer).toNat < 2 ^ bits :=
    (Nat.sub_le _ _).trans_lt (state.heap _).isLt
  unfold Ordinary.pointerValue at hd
  simp [InternalInput.code, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    InternalInput.targetAddress, Ordinary.pointerValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd,
    Nat.sub_eq_zero_iff_le, BitVec.add_assoc]
  simp only [← Nat.not_lt, ite_not]

theorem local_safe (physical : PhysicalROM) (pointer : Register) (heapWords : Nat) (state : WordState bits)
    (pointerRoom : (state.register .address + BitVec.ofNat bits (registerOffset pointer)).toNat < heapWords)
    (massRoom : (state.register .address + BitVec.ofNat bits 528).toNat < heapWords)
    (sizeRoom : (state.register .address + BitVec.ofNat bits 2).toNat < heapWords)
    (targetRoom : (InternalInput.targetAddress state pointer).toNat < heapWords) :
    PackedAccessSafe heapWords physical (InternalInput.code pointer) state := by
  simp [BitVec.toNat_add] at pointerRoom massRoom sizeRoom
  intro count hc
  change count < 25 at hc
  by_cases last : count = 24
  · subst count
    change ((executeOps physical ((InternalInput.code pointer).take 24) state).register .index).toNat < heapWords
    rw [index_target]
    exact targetRoom
  · have earlier : count < 24 := by omega
    interval_cases count <;>
      simp [InternalInput.code, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
        packingAccessFits, AccessFits]
    all_goals first | exact pointerRoom | exact massRoom | exact sizeRoom

end Generic

theorem target_room (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (pointer : Register) (state : WordState (bits q full))
    (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (data : RuntimeData.Data q full state.heap) (a : Nat)
    (hp : (Ordinary.pointerValue state pointer).toNat = a) (ha : a < 2 * t q full) :
    (InternalInput.targetAddress state pointer).toNat < allocated q full := by
  have hpfit : Fits (bits q full) a := by rw [← hp]; exact (Ordinary.pointerValue state pointer).isLt
  have hpword : Ordinary.pointerValue state pointer = BitVec.ofNat _ a := by
    rw [← hp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmass : state.heap (state.register .address + BitVec.ofNat _ 528) = BitVec.ofNat _ (full.length + q + 1) := by
    rw [base, BitVec.ofNat_add_ofNat]
    exact data.mass
  have hsize : state.heap (state.register .address + BitVec.ofNat _ 2) = BitVec.ofNat _ (t q full) := by
    rw [base, BitVec.ofNat_add_ofNat]
    exact data.size
  have hpow : 8 ≤ 2 ^ bits q full :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) ((by decide : 3 ≤ 32).trans (bits_room q full))
  have h4 : 4 < 2 ^ bits q full := by omega
  have h5 : 5 < 2 ^ bits q full := by omega
  unfold InternalInput.targetAddress
  rw [hpword, hmass, hsize]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpfit, Nat.mod_eq_of_lt (size_fits q full),
    packingArithmetic, Nat.mod_eq_of_lt (mass_fits q full), Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h5]
  by_cases hs : a < t q full
  · rw [ite_eq_left hs]
    have shape : state.register .address + (BitVec.ofNat _ ((full.length + q + 1) * 4) + BitVec.ofNat _ 533) +
        BitVec.ofNat _ a = BitVec.ofNat _ (controlBase q full + 533 + 4 * (full.length + q + 1) + a) := by
      rw [base, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
      congr 1
      omega
    rw [shape, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (RuntimeData.cache_address_fits q full hq 4 a (by decide) (by omega))]
    exact RuntimeData.cache_address_room q full 4 a (by decide) (by omega)
  · rw [ite_eq_right hs]
    have hn : a - t q full < t q full := by omega
    have shape : state.register .address + (BitVec.ofNat _ ((full.length + q + 1) * 5) + BitVec.ofNat _ 533) +
        BitVec.ofNat _ (a - t q full) =
        BitVec.ofNat _ (controlBase q full + 533 + 5 * (full.length + q + 1) + (a - t q full)) := by
      rw [base, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
      congr 1
      omega
    rw [shape, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (RuntimeData.cache_address_fits q full hq 5 (a - t q full) (by decide) (by omega))]
    exact RuntimeData.cache_address_room q full 5 (a - t q full) (by decide) (by omega)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.InternalAccess
