module

public import Structure.PSTR_BuildLower_InternalInput_030
public import Structure.PSTR_BuildLower_PreparedLayout_054

/-! Real parent/degree data at their agreed physical cache addresses. These
are materialized heap words, to be supplied by A06's producer OutputData;
they contain no execution, answer-selection, safety or cost certificate. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.InternalInput
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
variable {bits : Nat}

structure Data (q : Nat) (full : List (Finset (Fin q))) (base : Nat) (heap : BitVec bits → BitVec bits) : Prop where
  mass : heap (BitVec.ofNat bits (base + 528)) = BitVec.ofNat bits (full.length + q + 1)
  size : heap (BitVec.ofNat bits (base + 2)) = BitVec.ofNat bits (SourceFacts.size q full)
  parent : ∀ node : (prepareNormalization q full).indexed.NodeId,
    heap (BitVec.ofNat bits (base + 533 + 4 * (full.length + q + 1) + node.val)) =
      BitVec.ofNat bits ((givenTreeROM q full).internal.getD node.val 0)
  degree : ∀ node : (prepareNormalization q full).indexed.NodeId,
    heap (BitVec.ofNat bits (base + 533 + 5 * (full.length + q + 1) + node.val)) =
      BitVec.ofNat bits ((givenTreeROM q full).internal.getD (SourceFacts.size q full + node.val) 0)

theorem original_value (q : Nat) (full : List (Finset (Fin q))) (base a : Nat) (rom : PhysicalROM)
    (pointer : Register) (state : WordState bits) (data : Data q full base state.heap)
    (hbase : state.register .address = BitVec.ofNat bits base)
    (hp : (Ordinary.pointerValue state pointer).toNat = a)
    (ha : a < 2 * SourceFacts.size q full)
    (hM : Fits bits (full.length + q + 1)) (ht : Fits bits (SourceFacts.size q full)) (hbits : 3 ≤ bits) :
    (executeOps rom (code pointer) state).register .value =
      BitVec.ofNat bits ((givenTreeROM q full).semantic.read .internal a) := by
  have hpfit : Fits bits a := by rw [← hp]; exact (Ordinary.pointerValue state pointer).isLt
  have hpword : Ordinary.pointerValue state pointer = BitVec.ofNat bits a := by
    rw [← hp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmass : state.heap (state.register .address + BitVec.ofNat bits 528) =
      BitVec.ofNat bits (full.length + q + 1) := by
    rw [hbase, BitVec.ofNat_add_ofNat]
    exact data.mass
  have hsize : state.heap (state.register .address + BitVec.ofNat bits 2) =
      BitVec.ofNat bits (SourceFacts.size q full) := by
    rw [hbase, BitVec.ofNat_add_ofNat]
    exact data.size
  have hpow : 8 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbits
  have h4 : 4 < 2 ^ bits := by omega
  have h5 : 5 < 2 ^ bits := by omega
  rw [value]
  unfold targetAddress
  rw [hpword, hmass, hsize]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpfit, Nat.mod_eq_of_lt ht,
    packingArithmetic, Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h5]
  by_cases hs : a < SourceFacts.size q full
  · rw [ite_eq_left hs]
    have he : state.register .address + (BitVec.ofNat bits ((full.length + q + 1) * 4) + BitVec.ofNat bits 533) +
        BitVec.ofNat bits a = BitVec.ofNat bits (base + 533 + 4 * (full.length + q + 1) + a) := by
      rw [hbase, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
      congr 1
      omega
    rw [he]
    exact data.parent ⟨a, hs⟩
  · rw [ite_eq_right hs]
    have hn : a - SourceFacts.size q full < SourceFacts.size q full := by omega
    have he : state.register .address + (BitVec.ofNat bits ((full.length + q + 1) * 5) + BitVec.ofNat bits 533) +
        BitVec.ofNat bits (a - SourceFacts.size q full) =
        BitVec.ofNat bits (base + 533 + 5 * (full.length + q + 1) + (a - SourceFacts.size q full)) := by
      rw [hbase, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
      congr 1
      omega
    rw [he]
    have hd := data.degree ⟨a - SourceFacts.size q full, hn⟩
    have hi : SourceFacts.size q full + (a - SourceFacts.size q full) = a := by omega
    simpa only [hi, PhysicalROM.semantic, PhysicalROM.words] using hd

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.InternalInput
