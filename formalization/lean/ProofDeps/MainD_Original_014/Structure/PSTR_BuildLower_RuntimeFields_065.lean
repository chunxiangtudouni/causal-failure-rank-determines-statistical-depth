module

public import Structure.PSTR_BuildLower_RuntimeData_062

/-! True producer-bank fields give the scalar inputs consumed by actual
builder ports and Expr. All scalar Fits are derived from the common original
layout; none are additional original-caller inputs. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.RuntimeData
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout PA17ProgramTemplates041

theorem stageCount_fits (q : Nat) (full : List (Finset (Fin q))) : Fits (bits q full) full.length :=
  lt_of_le_of_lt (by omega) (mass_fits q full)

theorem toolCount_fits (q : Nat) (full : List (Finset (Fin q))) : Fits (bits q full) q :=
  lt_of_le_of_lt (by omega) (mass_fits q full)

theorem oldCapacity_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) : Fits (bits q full) (oldCapacity q full) := by
  have hw : 0 < CapacityBits.width q := by
    by_contra hn
    have hz : CapacityBits.width q = 0 := by omega
    have he := (CapacityBits.width_eq_zero_iff q).mp hz
    omega
  exact lt_of_le_of_lt ((oldCapacity_le q full hq).trans (Nat.le_mul_of_pos_right _ hw)) (capacity_product_fits q full hq)

theorem indexBase_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) : Fits (bits q full) (indexBase q full) :=
  lt_of_le_of_lt (Nat.le_add_right _ _) (ordinary_end_fits q full hq)

theorem Data.stages_nat (q : Nat) (full : List (Finset (Fin q))) (state : WordState (bits q full))
    (data : Data q full state.heap) (hb : state.register .address = BitVec.ofNat _ (controlBase q full)) :
    (state.heap (state.register .address)).toNat = full.length := by
  rw [hb, data.stages, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (stageCount_fits q full)]

theorem Data.tools_nat (q : Nat) (full : List (Finset (Fin q))) (state : WordState (bits q full))
    (data : Data q full state.heap) (hb : state.register .address = BitVec.ofNat _ (controlBase q full)) :
    (state.heap (state.register .address + BitVec.ofNat _ 1)).toNat = q := by
  rw [hb, BitVec.ofNat_add_ofNat, data.tools, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (toolCount_fits q full)]

theorem Data.cutoff_nat (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (state : WordState (bits q full))
    (data : Data q full state.heap) (hb : state.register .address = BitVec.ofNat _ (controlBase q full)) :
    (state.heap (state.register .address + BitVec.ofNat _ 3)).toNat = oldCapacity q full := by
  rw [hb, BitVec.ofNat_add_ofNat, data.cutoff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (oldCapacity_fits q full hq)]

theorem Data.index_nat (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (state : WordState (bits q full))
    (data : Data q full state.heap) (hb : state.register .address = BitVec.ofNat _ (controlBase q full)) :
    (state.heap (state.register .address + BitVec.ofNat _ 6)).toNat = indexBase q full := by
  rw [hb, BitVec.ofNat_add_ofNat, data.index, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (indexBase_fits q full hq)]

theorem Data.dimensions (q : Nat) (full : List (Finset (Fin q))) (state : WordState (bits q full))
    (data : Data q full state.heap) (hb : state.register .address = BitVec.ofNat _ (controlBase q full)) :
    ∀ address < 3, state.heap (state.register .address + BitVec.ofNat _ address) =
      BitVec.ofNat _ (((dimensionROM full.length q (t q full)).words .input).getD (BitVec.ofNat (bits q full) address).toNat 0) := by
  intro address ha
  have hp : 8 ≤ 2 ^ bits q full := Nat.pow_le_pow_right (by decide : 1 ≤ 2) ((by decide : 3 ≤ 32).trans (bits_room q full))
  have hf : Fits (bits q full) address := by change address < 2 ^ bits q full; omega
  rw [hb, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
  interval_cases address
  · simpa only [Nat.add_zero, dimensionROM, PhysicalROM.words, List.getD_cons_zero] using data.stages
  · simpa only [dimensionROM, PhysicalROM.words, List.getD_cons_succ, List.getD_cons_zero] using data.tools
  · simpa only [dimensionROM, PhysicalROM.words, List.getD_cons_succ, List.getD_cons_zero] using data.size

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.RuntimeData
