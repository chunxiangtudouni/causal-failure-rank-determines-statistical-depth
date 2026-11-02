module

public import Structure.PSTR_BuildLower_LoadData_064

/-! The actual inline ALU step preserves producer data and all other lexical
bank words in addition to source simulation. Common original-layout room is
discharged internally; hardware scratch arithmetic stays direct Word. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem alu_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (op : ValueOp) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (hf : ∀ reg, Fits (bits q full) (logical.register reg))
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ op.relativeLower ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ op.relativeLower ++ right).length)) :
    let after := packingRun physical (left ++ op.relativeLower ++ right) op.relativeLower.length state
    op.relativeLower.length ≤ 13 ∧
      Prepared q full (op.original.execute (givenTreeROM q full).semantic logical) after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + op.relativeLower.length)) ∧ after.halted = false ∧
      ∀ offset ≤ 512, offset ≠ registerOffset op.target →
        after.heap (BitVec.ofNat _ (controlBase q full + offset)) = state.heap (BitVec.ofNat _ (controlBase q full + offset)) := by
  have actual := literal_alu q (oldCapacity q full) (capacity q full) (indexBase q full) (indexWords q full) (controlBase q full)
    (givenTreeROM q full) physical op logical state hrep hf
    (by have hh := bits_room q full; omega) (bank_offset_fits q full hq 39 (by decide)) (oldCapacity_le q full hq)
    le_rfl (by have hh := ordinary_before_control q full; omega) left right hpc ha hcode hpcfit
  have heapEq : (packingRun physical (left ++ op.relativeLower ++ right) op.relativeLower.length state).heap =
      Function.update state.heap (BitVec.ofNat _ (controlBase q full + registerOffset op.target))
        (op.value (portRegisters (BitVec.ofNat _ (controlBase q full)) state.heap)) := by
    rw [ValueStep.run op physical left right state hpc ha hcode hpcfit, relativeValue_heap, hrep.address, BitVec.ofNat_add_ofNat]
  dsimp only at actual ⊢
  refine ⟨actual.1, actual.2.1, ?_, actual.2.2.1, actual.2.2.2, ?_⟩
  · rw [heapEq]
    exact RuntimeData.Data.vm_update q full hq state.heap data op.target _
  · intro offset ho hn
    rw [heapEq]
    exact RuntimeData.vm_update_offset q full hq state.heap op.target _ offset ho hn

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
