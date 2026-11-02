module

public import Structure.PSTR_BuildLower_ASTShape_075
public import Structure.PSTR_BuildLower_LoopSource_077

/-! A compositional bound for the actual structured lowering: each source
instruction costs at most206, each repeated body pays its real14-op control,
and every invocation pays its actual expression/save/restore setup. This
file only compares that explicit budget to ORIGINAL source-list length;
actual execution is proved separately and is not a hypothesis here. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ASTBudget
open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17ProgramTemplates041

def budget : Program → PhysicalROM → Nat
  | .code ops, _ => 206 * ops.length
  | .append first second, rom => budget first rom + budget second rom
  | .repeat _ bound body, rom => (fixedExprCode bound).length + 9 +
      bound.eval rom (fun _ => 0) * (budget body rom + 14) + 11

def factor : Program → Nat
  | .code _ => 206
  | .append first second => factor first + factor second
  | .repeat _ _ body => 2 * factor body + 237

theorem factor_positive (program : Program) : 0 < factor program := by
  induction program with
  | code ops => change 0 < 206; decide
  | append first second ihl ihr => change 0 < factor first + factor second; omega
  | «repeat» counter bound body ih => change 0 < 2 * factor body + 237; omega

theorem budget_le_source (program : Program) (rom : PhysicalROM) (environment : Nat → Nat)
    (hs : ASTShape.Shape program) (hl : ExprBounds.programLoopsCertified program = true)
    (hn : ProgramShape.nonemptyBodies program = true) :
    budget program rom ≤ factor program * ((program.eval rom environment).length + 1) := by
  induction program generalizing environment with
  | code ops =>
    simp only [budget, factor, Program.eval, instructions, List.length_map]
    omega
  | append first second ihl ihr =>
    have hloops := Bool.and_eq_true_iff.mp hl
    have hnonempty := Bool.and_eq_true_iff.mp hn
    have hleft := ihl environment hs.1 hloops.1 hnonempty.1
    have hright := ihr environment hs.2 hloops.2 hnonempty.2
    simp only [budget, factor, Program.eval, List.length_append]
    nlinarith [Nat.zero_le (factor first * (second.eval rom environment).length),
      Nat.zero_le (factor second * (first.eval rom environment).length)]
  | «repeat» counter bound body ih =>
    have hloops := Bool.and_eq_true_iff.mp hl
    have hnonempty := Bool.and_eq_true_iff.mp hn
    have hbody := ih environment hs.2.2.2.2 hloops.2 hnonempty.2
    have hpositive := ProgramShape.hasStep_positive body rom environment hnonempty.1
    have hbound := ProgramShape.zero_cells_eval bound hs.2.2.1 rom environment (fun _ => 0)
    have hlength : ((Program.repeat counter bound body).eval rom environment).length =
        bound.eval rom (fun _ => 0) * (body.eval rom environment).length := by
      rw [LoopSource.eval_repeat, LoopSource.code_length rom environment counter body hloops.2, hbound]
    have hsetup : (fixedExprCode bound).length + 9 + 11 ≤ 223 := by
      have hh := fixedExprCode_length bound
      have hsize := hs.2.1
      omega
    have hinner : budget body rom + 14 ≤ (2 * factor body + 14) * (body.eval rom environment).length := by
      have hdouble : (body.eval rom environment).length + 1 ≤ 2 * (body.eval rom environment).length := by omega
      have hscaled := Nat.mul_le_mul_left (factor body) hdouble
      nlinarith
    have hscaled := Nat.mul_le_mul_left (bound.eval rom (fun _ => 0)) hinner
    have hfactor := Nat.mul_le_mul_right
      (bound.eval rom (fun _ => 0) * (body.eval rom environment).length)
      (show 2 * factor body + 14 ≤ 2 * factor body + 237 by omega)
    rw [hlength]
    simp only [budget, factor]
    nlinarith

theorem fullBuild_budget (rom : PhysicalROM) (environment : Nat → Nat) :
    budget fullBuild rom ≤ factor fullBuild * ((fullBuild.eval rom environment).length + 1) :=
  budget_le_source fullBuild rom environment ASTShape.fullBuild_shape ExprBounds.fullBuild_loops_certified
    ProgramShape.fullBuild_nonemptyBodies

theorem fullBuild_budget_original (N q t : Nat) (environment : Nat → Nat) :
    budget fullBuild (dimensionROM N q t) ≤
      factor fullBuild * ((PA17TableBuild005.buildProgram N q t).length + 1) := by
  simpa only [fullBuild_eval] using fullBuild_budget (dimensionROM N q t) environment

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ASTBudget
