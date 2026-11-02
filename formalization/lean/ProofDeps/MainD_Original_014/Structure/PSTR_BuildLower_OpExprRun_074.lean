module

public import Structure.PSTR_BuildLower_LiteralRun_072
public import Structure.PSTR_BuildLower_DynamicData_069

/-! Actual fixed typed-AST instruction execution. Dynamic Expr constants use
the inline runtime compiler; literals use concrete ports. No dimension-derived
source immediate is substituted as a physical code literal. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

def OpExprShape : OpExpr → Prop
  | .constant _ expr => expr.size ≤ 29 ∧ expressionCellLimit expr ≤ 21 ∧ expressionInputLimit expr ≤ 3
  | .literal _ => True

def OpExprFits (q : Nat) (full : List (Finset (Fin q))) (environment : Nat → Nat) : OpExpr → Prop
  | .constant _ expr => ExprBounds.nodesFit (bits q full) (dimensionROM full.length q (t q full)) environment expr
  | .literal _ => True

def OpExprRuns (q : Nat) (full : List (Finset (Fin q))) (physical : PhysicalROM) (op : OpExpr) (environment : Nat → Nat)
    (logical : State) (state : WordState (bits q full)) (left right : List PackingOp) : Prop :=
  ∃ count ≤ 206,
    let block := lowerOpExpr ConcreteAST.ports left.length op
    let after := packingRun physical (left ++ block ++ right) count state
    Prepared q full ((op.eval (dimensionROM full.length q (t q full)) environment).execute (givenTreeROM q full).semantic logical) after ∧
      RuntimeData.Data q full after.heap ∧ after.pc = BitVec.ofNat _ (5 * (left.length + block.length)) ∧ after.halted = false ∧
      ∀ offset < 128, (offset < 32 ∨ 39 ≤ offset) →
        after.heap (BitVec.ofNat _ (controlBase q full + offset)) = state.heap (BitVec.ofNat _ (controlBase q full + offset))

theorem opExpr_run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (op : OpExpr) (environment : Nat → Nat)
    (later : List Op) (logical : State)
    (context : SourceContext.Context q full (op.eval (dimensionROM full.length q (t q full)) environment :: later) logical)
    (state : WordState (bits q full)) (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (hshape : OpExprShape op) (hvalues : OpExprFits q full environment op)
    (henv : ∀ address < 21, state.heap (state.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address))
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ lowerOpExpr ConcreteAST.ports left.length op ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ lowerOpExpr ConcreteAST.ports left.length op ++ right).length)) :
    OpExprRuns q full (CompactControllerClaims.controllerInput q full used) op environment logical state left right := by
  let runtime := CompactControllerClaims.controllerInput q full used
  cases op with
  | literal original =>
    obtain ⟨count, hc, result⟩ := literal_run q full used hq hlaminar original later logical context state hrep data left right hpc ha
      (by simpa only [lowerOpExpr] using hcode) (by simpa only [lowerOpExpr] using hpcfit)
    refine ⟨count, hc.trans (by decide), ?_⟩
    simpa only [lowerOpExpr, OpExpr.eval] using result
  | constant target expr =>
    have actual := dynamic_data q full hq runtime target expr environment logical state hrep data hshape.2.1 hshape.2.2 hshape.1
      (by intro address ha; exact henv address (ha.trans_le hshape.2.1)) hvalues left right hpc ha
      (by simpa only [lowerOpExpr, DynamicStep.code] using hcode) (by simpa only [lowerOpExpr, DynamicStep.code] using hpcfit)
    refine ⟨(DynamicStep.code target expr).length, actual.1, ?_⟩
    dsimp only
    refine ⟨actual.2.1, actual.2.2.1, actual.2.2.2.1, actual.2.2.2.2.1, ?_⟩
    intro offset ho hout
    have hlo := (registerSlot_bounds target).1
    have hhi := (registerSlot_bounds target).2
    change 32 ≤ registerOffset target at hlo
    change registerOffset target < 39 at hhi
    exact actual.2.2.2.2.2 offset (by omega) (by rcases hout with h | h <;> omega) (Or.inl ho)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
