module

public import Structure.PSTR_BuildLower_ProgramShape_073
public import Structure.PSTR_BuildLower_SourceContext_052
public import Structure.PSTR_BuildLower_PreparedLayout_054

/-! Exact source slices for the actual countdown induction. The source is
the original reversed range, so a count n+1 executes environment(counter:=n+1)
first. Body lengths are independent of the lexical counter only because the
fixed AST's loop bounds were proved to have no lexical cells. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopSource
open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17ProgramTemplates041

def code (rom : PhysicalROM) (environment : Nat → Nat) (counter : Nat) (body : Program) (count : Nat) : List Op :=
  (List.range count).reverse.flatMap (fun index => body.eval rom (Function.update environment counter (index + 1)))

theorem code_zero (rom : PhysicalROM) (environment : Nat → Nat) (counter : Nat) (body : Program) :
    code rom environment counter body 0 = [] := rfl

theorem code_succ (rom : PhysicalROM) (environment : Nat → Nat) (counter : Nat) (body : Program) (count : Nat) :
    code rom environment counter body (count + 1) =
      body.eval rom (Function.update environment counter (count + 1)) ++ code rom environment counter body count := by
  simp only [code, List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.flatMap_cons]

theorem eval_repeat (rom : PhysicalROM) (environment : Nat → Nat) (counter : Nat) (bound : Expr) (body : Program) :
    (Program.repeat counter bound body).eval rom environment = code rom environment counter body (bound.eval rom environment) := rfl

theorem code_length (rom : PhysicalROM) (environment : Nat → Nat) (counter : Nat) (body : Program)
    (hc : ExprBounds.programLoopsCertified body = true) (count : Nat) :
    (code rom environment counter body count).length = count * (body.eval rom environment).length := by
  induction count with
  | zero => simp only [code_zero, List.length_nil, Nat.zero_mul]
  | succ count ih =>
    rw [code_succ, List.length_append, ih,
      ProgramShape.eval_length_congr body rom (Function.update environment counter (count + 1)) environment hc]
    ring

def iterationContext (q : Nat) (full : List (Finset (Fin q))) (environment : Nat → Nat)
    (counter : Nat) (body : Program) (count : Nat) (logical : State)
    (context : SourceContext.Context q full
      (code (dimensionROM full.length q (PreparedLayout.t q full)) environment counter body (count + 1)) logical) :
    SourceContext.Context q full
      (body.eval (dimensionROM full.length q (PreparedLayout.t q full)) (Function.update environment counter (count + 1))) logical :=
  SourceContext.left (code_succ _ _ _ _ _ ▸ context)

def remainingContext (q : Nat) (full : List (Finset (Fin q))) (environment : Nat → Nat)
    (counter : Nat) (body : Program) (count : Nat) (logical : State)
    (context : SourceContext.Context q full
      (code (dimensionROM full.length q (PreparedLayout.t q full)) environment counter body (count + 1)) logical) :
    SourceContext.Context q full
      (code (dimensionROM full.length q (PreparedLayout.t q full)) environment counter body count)
      (IndexedClosureRAM.execute (givenTreeROM q full).semantic
        (body.eval (dimensionROM full.length q (PreparedLayout.t q full)) (Function.update environment counter (count + 1))) logical) :=
  SourceContext.right (code_succ _ _ _ _ _ ▸ context)

theorem execute_succ (rom source : PhysicalROM) (environment : Nat → Nat) (counter : Nat)
    (body : Program) (count : Nat) (logical : State) :
    IndexedClosureRAM.execute source.semantic (code rom environment counter body (count + 1)) logical =
      IndexedClosureRAM.execute source.semantic (code rom environment counter body count)
        (IndexedClosureRAM.execute source.semantic (body.eval rom (Function.update environment counter (count + 1))) logical) := by
  rw [code_succ, IndexedClosureRAM.execute_append]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopSource
