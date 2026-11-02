module

public import Structure.PSTR_BuildLower_RuntimeData_062
public import Structure.PSTR_BuildLower_LoadFinish_050

/-! Real VM writeback preserves the materialized runtime producer data and
all other lexical bank words. Common-layout arithmetic discharges the room
conditions internally. This is a fetched3-op suffix, not a free source update. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.RuntimeData
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem Data.vm_update (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (heap : BitVec (bits q full) → BitVec (bits q full)) (data : Data q full heap)
    (target : Register) (value : BitVec (bits q full)) :
    Data q full (Function.update heap (BitVec.ofNat _ (controlBase q full + registerOffset target)) value) := by
  have hlo := (registerSlot_bounds target).1
  have hhi := (registerSlot_bounds target).2
  change 32 ≤ registerOffset target at hlo
  change registerOffset target < 39 at hhi
  have ht : Fits (bits q full) (controlBase q full + registerOffset target) :=
    bank_offset_fits q full hq _ (by omega)
  have hb : 4 ≤ controlBase q full := by unfold controlBase; omega
  apply Data.of_frame q full hq heap _ data
  · intro point hp
    rw [Function.update_of_ne (word_address_ne (lt_of_le_of_lt (by omega) ht) ht (by omega))]
  · intro offset ho
    rw [Function.update_of_ne (word_address_ne (bank_offset_fits q full hq offset (by omega)) ht (by omega))]
  · intro point hp hf
    rw [Function.update_of_ne (word_address_ne hf ht (by omega))]

theorem vm_update_offset (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (heap : BitVec (bits q full) → BitVec (bits q full)) (target : Register) (value : BitVec (bits q full))
    (offset : Nat) (ho : offset ≤ 512) (hne : offset ≠ registerOffset target) :
    Function.update heap (BitVec.ofNat _ (controlBase q full + registerOffset target)) value
      (BitVec.ofNat _ (controlBase q full + offset)) = heap (BitVec.ofNat _ (controlBase q full + offset)) := by
  have hh := (registerSlot_bounds target).2
  change registerOffset target < 39 at hh
  exact Function.update_of_ne
    (word_address_ne (bank_offset_fits q full hq offset ho)
      (bank_offset_fits q full hq (registerOffset target) (by omega)) (by omega)) _ _

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.RuntimeData

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

abbrev Prepared (q : Nat) (full : List (Finset (Fin q))) (logical : State) (physical : WordState (bits q full)) : Prop :=
  Represents q (oldCapacity q full) (capacity q full) (indexBase q full) (indexWords q full) (controlBase q full) logical physical

theorem finish_load_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (target : Register) (value : Nat) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (hvalue : state.register .value = BitVec.ofNat _ value)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeWrite (registerOffset target) ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeWrite (registerOffset target) ++ right).length)) :
    let after := packingRun physical (left ++ relativeWrite (registerOffset target) ++ right) 3 state
    Prepared q full (loaded logical target value) after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + 3)) ∧ after.halted = false ∧
      ∀ offset ≤ 512, offset ≠ registerOffset target →
        after.heap (BitVec.ofNat _ (controlBase q full + offset)) = state.heap (BitVec.ofNat _ (controlBase q full + offset)) := by
  have final := finish_load q (oldCapacity q full) (capacity q full) (indexBase q full) (indexWords q full)
    (controlBase q full) physical target value logical state hrep hvalue
    (by have hh := bits_room q full; omega) (bank_offset_fits q full hq 39 (by decide))
    (oldCapacity_le q full hq) le_rfl (by have hh := ordinary_before_control q full; omega)
    left right hpc ha hcode hpcfit
  have hr : packingRun physical (left ++ relativeWrite (registerOffset target) ++ right) 3 state =
      executeOps physical (relativeWrite (registerOffset target)) state := by
    have hh := straight_prefix physical left (relativeWrite (registerOffset target)) right state
      (relativeWrite_straight _) hcode hpcfit hpc ha 3 (by rw [relativeWrite_length])
    rw [List.take_of_length_le (by rw [relativeWrite_length])] at hh
    exact hh
  have heapEq : (packingRun physical (left ++ relativeWrite (registerOffset target) ++ right) 3 state).heap =
      Function.update state.heap (BitVec.ofNat _ (controlBase q full + registerOffset target)) (state.register .value) := by
    rw [hr, relativeWrite_heap, hrep.address, BitVec.ofNat_add_ofNat]
  dsimp only at final ⊢
  refine ⟨final.1, ?_, final.2.1, final.2.2, ?_⟩
  · rw [heapEq]
    exact RuntimeData.Data.vm_update q full hq state.heap data target (state.register .value)
  · intro offset ho hn
    rw [heapEq]
    exact RuntimeData.vm_update_offset q full hq state.heap target (state.register .value) offset ho hn

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
