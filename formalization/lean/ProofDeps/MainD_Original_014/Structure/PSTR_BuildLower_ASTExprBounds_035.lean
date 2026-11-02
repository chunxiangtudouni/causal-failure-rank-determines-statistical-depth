module

public import Structure.PSTR_BuildLower_ExprBounds_032

/-! Every actual logical fullBuild loop environment has bounded dynamic
Expr nodes. Bounds follow the ORIGINAL Program.eval lexical updates; no
successful run, DP performance or whole-backend no-wrap oracle is assumed. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ExprBounds
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PA17UniformGenerator035b PA17ProgramTemplates041

private theorem below_zero (expr : Expr) (h : expressionCellLimit expr = 0) : expr.Below 0 := by
  induction expr with
  | constant value => trivial
  | cell address => simp [expressionCellLimit] at h
  | input address => trivial
  | binary operation left right ihl ihr =>
    have hl : expressionCellLimit left = 0 := by change max _ _ = 0 at h; omega
    have hr : expressionCellLimit right = 0 := by change max _ _ = 0 at h; omega
    exact ⟨ihl hl, ihr hr⟩

def loopCertified (expr : Expr) : Bool := arithmetic expr &&
  decide (expressionCellLimit expr = 0 ∧ coefficient expr ≤ 4 ∧ degree expr ≤ 1)

def programLoopsCertified : Program → Bool
  | .code _ => true
  | .append left right => programLoopsCertified left && programLoopsCertified right
  | .repeat _ bound body => loopCertified bound && programLoopsCertified body

theorem fullBuild_loops_certified : programLoopsCertified fullBuild = true := by decide

theorem loop_bound_le (expr : Expr) (rom : PhysicalROM) (environment : Nat → Nat) (B : Nat)
    (hB : 1 ≤ B) (hc : loopCertified expr = true)
    (hd : ∀ address, rom.semantic.read .input address ≤ B) : expr.eval rom environment ≤ 4 * B := by
  rcases Bool.and_eq_true_iff.mp hc with ⟨ha, hn⟩
  have nums : expressionCellLimit expr = 0 ∧ coefficient expr ≤ 4 ∧ degree expr ≤ 1 := of_decide_eq_true hn
  have he := Expr.eval_congr expr rom 0 (below_zero expr nums.1) environment (fun _ => 0) (by intro address ha; omega)
  rw [← he]
  have hh := eval_le expr rom (fun _ => 0) B hB ha (fun _ => Nat.zero_le _) hd
  exact hh.trans (by simpa only [pow_one] using Nat.mul_le_mul nums.2.1 (Nat.pow_le_pow_right hB nums.2.2))

def allExprNodesFit (bits : Nat) (rom : PhysicalROM) (environment : Nat → Nat) : Program → Prop
  | .code ops => ∀ op ∈ ops, match op with
      | .constant _ expr => nodesFit bits rom environment expr
      | .literal _ => True
  | .append left right => allExprNodesFit bits rom environment left ∧ allExprNodesFit bits rom environment right
  | .repeat counter bound body => nodesFit bits rom environment bound ∧
      ∀ index < bound.eval rom environment,
        allExprNodesFit bits rom (Function.update environment counter (index + 1)) body

theorem allExprNodesFit_of_certified (bits : Nat) (program : Program) (rom : PhysicalROM)
    (environment : Nat → Nat) (B : Nat) (hB : 1 ≤ B)
    (hfit : Fits bits (65536 * (4 * B) ^ 3))
    (hd : ∀ address, rom.semantic.read .input address ≤ B)
    (henv : ∀ address, environment address ≤ 4 * B)
    (hp : programCertified program = true) (hl : programLoopsCertified program = true) :
    allExprNodesFit bits rom environment program := by
  have exprFit (expr : Expr) (env : Nat → Nat) (he : certified expr = true)
      (hvars : ∀ address, env address ≤ 4 * B) : nodesFit bits rom env expr := by
    rcases Bool.and_eq_true_iff.mp he with ⟨ha, hn⟩
    have nums : coefficient expr ≤ 65536 ∧ degree expr ≤ 3 := of_decide_eq_true hn
    exact nodesFit_of_envelope bits expr rom env (4 * B) (by omega) ha nums.1 nums.2
      hvars (fun address => (hd address).trans (by omega)) hfit
  induction program generalizing environment with
  | code ops =>
    intro op hm
    have hh := (List.all_eq_true.mp hp) op hm
    cases op with
    | constant target expr => exact exprFit expr environment hh henv
    | literal original => trivial
  | append left right ihl ihr =>
    exact ⟨ihl environment henv (Bool.and_eq_true_iff.mp hp).1 (Bool.and_eq_true_iff.mp hl).1,
      ihr environment henv (Bool.and_eq_true_iff.mp hp).2 (Bool.and_eq_true_iff.mp hl).2⟩
  | «repeat» counter bound body ih =>
    refine ⟨exprFit bound environment (Bool.and_eq_true_iff.mp hp).1 henv, ?_⟩
    intro index hi
    have hcount := loop_bound_le bound rom environment B hB (Bool.and_eq_true_iff.mp hl).1 hd
    have hnew : ∀ address, Function.update environment counter (index + 1) address ≤ 4 * B := by
      intro address
      by_cases he : address = counter
      · subst address
        rw [Function.update_self]
        omega
      · rw [Function.update_of_ne he]
        exact henv address
    exact ih (Function.update environment counter (index + 1)) hnew
      (Bool.and_eq_true_iff.mp hp).2 (Bool.and_eq_true_iff.mp hl).2

private theorem four_cubic_fits (N q : Nat) :
    Fits (indexWidth 32 N q) (65536 * (4 * (N + q + 2)) ^ 3) := by
  apply fits_indexWidth_of_lt_power
  let B := N + q + 2
  have hb : 2 ≤ B := by dsimp only [B]; omega
  have hp : 4194304 < B ^ 29 :=
    lt_of_lt_of_le (by decide : 4194304 < 2 ^ 29) (Nat.pow_le_pow_left hb 29)
  have hpos : 0 < B ^ 3 := pow_pos (by omega) _
  have he : 65536 * (4 * B) ^ 3 = 4194304 * B ^ 3 := by ring
  change 65536 * (4 * B) ^ 3 < B ^ 32
  rw [he]
  calc
    _ < B ^ 3 * B ^ 29 := by nlinarith
    _ = B ^ 32 := by rw [← pow_add]

theorem fullBuild_initial_nodesFit (N q t : Nat) (ht : t ≤ N + q + 1) :
    allExprNodesFit (indexWidth 32 N q) (dimensionROM N q t) (fun _ => 0) fullBuild := by
  have hd : ∀ address, (dimensionROM N q t).semantic.read .input address ≤ N + q + 2 := by
    intro address
    cases address with
    | zero => change N ≤ N + q + 2; omega
    | succ address => cases address with
      | zero => change q ≤ N + q + 2; omega
      | succ address => cases address with
        | zero => change t ≤ N + q + 2; omega
        | succ address => change 0 ≤ N + q + 2; omega
  exact allExprNodesFit_of_certified _ fullBuild _ (fun _ => 0) (N + q + 2) (by omega)
    (four_cubic_fits N q) hd (fun _ => Nat.zero_le _) fullBuild_certified fullBuild_loops_certified

theorem prepared_fullBuild_initial_nodesFit (q : Nat) (full : List (Finset (Fin q))) :
    allExprNodesFit (indexWidth 32 full.length q)
      (dimensionROM full.length q (prepareNormalization q full).indexed.nodes.size) (fun _ => 0) fullBuild :=
  fullBuild_initial_nodesFit full.length q _ (prepared_indexed_size_le q full)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ExprBounds
