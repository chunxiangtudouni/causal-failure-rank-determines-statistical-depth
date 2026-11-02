module

public import Structure.PSTR_BuildLower_ResourceTrace_094
public import Structure.PSTR_BuildLower_ALUData_068
public import Structure.PSTR_BuildLower_DynamicData_069

/-! Source simulation and resource preservation share the EXACT concrete
inline instruction count. Every fetched prefix protects full NEW-C capacity
and all fitted high-cache words; the bank frame is derived from real code. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

theorem alu_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (op : ValueOp) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hf : ∀ reg, Fits (bits q full) (logical.register reg))
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ op.relativeLower ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ op.relativeLower ++ right).length)) :
    let after := packingRun physical (left ++ op.relativeLower ++ right) op.relativeLower.length state
    op.relativeLower.length ≤ 13 ∧
      Prepared q full (op.original.execute (givenTreeROM q full).semantic logical) after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + op.relativeLower.length)) ∧ after.halted = false ∧
      (∀ offset ≤ 512, offset ≠ registerOffset op.target → after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
        state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      ResourceTrace.Keeps q full physical (left ++ op.relativeLower ++ right) state op.relativeLower.length := by
  have actual := alu_data q full hq physical op logical state hrep data hf left right hpc ha hcode hpcfit
  exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2.1, actual.2.2.2.2.1, actual.2.2.2.2.2,
    ResourceTrace.bank_actual_keeps q full hq physical op.relativeLower 32 39 (by decide) (by decide)
      (value_range op physical) (relativeValue_straight op) state hrep.address bounded left right hpc ha hcode hpcfit⟩

theorem dynamic_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (target : Register) (expr : Expr) (environment : Nat → Nat) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap)
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
      (∀ offset ≤ 512, offset ≠ registerOffset target → (offset < 128 ∨ 128 + expr.size ≤ offset) →
        after.heap (BitVec.ofNat _ (controlBase q full + offset)) = state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      ResourceTrace.Keeps q full physical (left ++ block ++ right) state block.length := by
  have actual := dynamic_data q full hq physical target expr environment logical state hrep data hc hd hs hcell hvalues
    left right hpc ha hcode hpcfit
  exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2.1, actual.2.2.2.2.1, actual.2.2.2.2.2,
    ResourceTrace.bank_actual_keeps q full hq physical (DynamicStep.code target expr) 32 (max 39 (128 + expr.size))
      (by have hh := Nat.le_max_left 39 (128 + expr.size); omega) (by omega)
      (ViewFrame.dynamic_range physical target expr) (DynamicStep.code_straight target expr)
      state hrep.address bounded left right hpc ha hcode hpcfit⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
