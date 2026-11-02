module

public import Structure.PSTR_BuildLower_LoadData_064
public import Structure.PSTR_BuildLower_RuntimeFields_065
public import Structure.PSTR_BuildLower_LexicalFrame_063
public import Structure.PSTR_BuildLower_DynamicRep_049

/-! An actual dynamic source instruction preserves all materialized runtime
data and disjoint lexical words. Only the original source Expr node bounds
are used; the packed backend is never transported through an all-Nat guard. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

theorem dynamic_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (target : Register) (expr : Expr) (environment : Nat → Nat) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (hc : expressionCellLimit expr ≤ 21) (hd : expressionInputLimit expr ≤ 3) (hs : expr.size ≤ 29)
    (hcell : ∀ address < expressionCellLimit expr,
      state.heap (state.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address))
    (hvalues : ExprBounds.nodesFit (bits q full) (dimensionROM full.length q (t q full)) environment expr)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ DynamicStep.code target expr ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ DynamicStep.code target expr ++ right).length)) :
    let block := DynamicStep.code target expr
    let after := packingRun physical (left ++ block ++ right) block.length state
    block.length ≤ 206 ∧
      Prepared q full ((Op.base (.constant target (expr.eval (dimensionROM full.length q (t q full)) environment))).execute
        (givenTreeROM q full).semantic logical) after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + block.length)) ∧ after.halted = false ∧
      ∀ offset ≤ 512, offset ≠ registerOffset target → (offset < 128 ∨ 128 + expr.size ≤ offset) →
        after.heap (BitVec.ofNat _ (controlBase q full + offset)) = state.heap (BitVec.ofNat _ (controlBase q full + offset)) := by
  have tempRoom : Fits (bits q full) (controlBase q full + max 39 (128 + expr.size)) :=
    bank_offset_fits q full hq _ (by omega)
  have ht : 128 + expr.size ≤ 2 ^ bits q full := by
    change controlBase q full + max 39 (128 + expr.size) < 2 ^ bits q full at tempRoom
    have hh := Nat.le_max_right 39 (128 + expr.size)
    omega
  have hhi : max 39 (128 + expr.size) ≤ 2 ^ bits q full := by
    change controlBase q full + max 39 (128 + expr.size) < 2 ^ bits q full at tempRoom
    omega
  have actual := dynamic q (oldCapacity q full) (capacity q full) (indexBase q full) (indexWords q full) (controlBase q full)
    (dimensionROM full.length q (t q full)) physical target expr environment logical state hrep (by omega) hd hcell
    (by intro address had; exact RuntimeData.Data.dimensions q full state data hrep.address address (had.trans_le hd))
    hvalues tempRoom (oldCapacity_le q full hq) le_rfl (by have hh := ordinary_before_control q full; omega)
    left right hpc ha hcode hpcfit
  have hr := DynamicStep.run target expr physical left right state hpc ha hcode hpcfit
  have hf := ViewFrame.dynamic_range (bits := bits q full) physical target expr
  have resultData : RuntimeData.Data q full
      (packingRun physical (left ++ DynamicStep.code target expr ++ right) (DynamicStep.code target expr).length state).heap := by
    apply RuntimeData.Data.of_frame q full hq state.heap _ data
    · intro point hp
      rw [hr]
      have hb : point < controlBase q full + 32 := by unfold controlBase; omega
      have hh := ViewFrame.bankRange_below physical (DynamicStep.code target expr) 32 (max 39 (128 + expr.size)) hf
        (by have h := Nat.le_max_left 39 (128 + expr.size); omega) state (controlBase q full) point hrep.address tempRoom hb
        (DynamicStep.code target expr).length
      simpa only [List.take_length] using hh
    · intro offset ho
      rw [hr]
      have hoff : Fits (bits q full) offset := by change offset < 2 ^ bits q full; omega
      have hh := ControlDataFrame.range_offset physical (DynamicStep.code target expr) 32 (max 39 (128 + expr.size)) hf hhi
        offset hoff (Or.inl ho) state (DynamicStep.code target expr).length
      simpa only [List.take_length, hrep.address, BitVec.ofNat_add_ofNat] using hh
    · intro point hp hfit
      rw [hr]
      have hoff : Fits (bits q full) (point - controlBase q full) := (Nat.sub_le _ _).trans_lt hfit
      have he : controlBase q full + (point - controlBase q full) = point := by omega
      have hout : max 39 (128 + expr.size) ≤ point - controlBase q full := by omega
      have hh := ControlDataFrame.range_offset physical (DynamicStep.code target expr) 32 (max 39 (128 + expr.size)) hf hhi
        (point - controlBase q full) hoff (Or.inr hout) state (DynamicStep.code target expr).length
      simpa only [List.take_length, hrep.address, BitVec.ofNat_add_ofNat, he] using hh
  dsimp only at actual ⊢
  refine ⟨(DynamicStep.code_length target expr).trans (by omega), actual.1, resultData, actual.2.1, actual.2.2, ?_⟩
  intro offset ho hn hout
  have hoff : Fits (bits q full) offset := lt_of_le_of_lt (by omega) (bank_offset_fits q full hq offset ho)
  have hh := ControlDataFrame.dynamic_actual_offset physical left right target expr offset hoff ht hn hout state hcode hpcfit hpc ha
  simpa only [hrep.address, BitVec.ofNat_add_ofNat] using hh

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
