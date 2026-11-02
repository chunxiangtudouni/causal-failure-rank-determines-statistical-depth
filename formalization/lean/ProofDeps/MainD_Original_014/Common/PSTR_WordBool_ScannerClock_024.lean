module

public import Common.PSTR_WordBool_ScannerStatement_023
public import Mathlib.Tactic.Ring

/-! Linear-in-workspace clocks for the actual scanner path. Both the action
count and push allowance are derived from fixed source syntax. Occupancy is
never replaced by elapsed computation time. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.ScannerClock

open Turing AuxWorkspace ScannerStatement

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

def actions : TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next | .peek _ _ next | .pop _ _ next => actions next + 1
  | .load _ next => actions next
  | .branch _ yes no => max (actions yes) (actions no)
  | .goto _ | .halt => 0

omit [DecidableEq K] in
theorem add_envelope (entry exit rest count span : Nat)
    (localBound : entry + exit + 2 ≤ 2 * span)
    (tailBound : rest ≤ 2 * count * span) :
    entry + exit + 2 + rest ≤ 2 * (count + 1) * span := by
  calc
    entry + exit + 2 + rest ≤ 2 * span + 2 * count * span := Nat.add_le_add localBound tailBound
    _ = 2 * (count + 1) * span := by ring

theorem clock_bound (statement : TM2.Stmt Γ Λ σ) (store : σ) (slots : ∀ k, List (Γ k))
    (bound : Nat) (bounded : ∀ k, (slots k).length ≤ bound) :
    clock statement store slots ≤ 2 * actions statement * (bound + pushes statement + 1) := by
  induction statement generalizing store slots bound with
  | push k value next ih =>
    have tail := ih store (Function.update slots k (value store :: slots k)) (bound + 1)
      (updated_push_bound store slots bound bounded k value)
    have tailBound : clock next store (Function.update slots k (value store :: slots k)) ≤
        2 * actions next * (bound + (pushes next + 1) + 1) := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tail
    have localBound : (slots k).length + (value store :: slots k).length + 2 ≤
        2 * (bound + (pushes next + 1) + 1) := by
      have entry := bounded k
      simp only [List.length_cons]
      omega
    exact add_envelope _ _ _ _ _ localBound tailBound
  | peek k value next ih =>
    have tail := ih (value store (slots k).head?) slots bound bounded
    have localBound : (slots k).length + (slots k).length + 2 ≤
        2 * (bound + pushes next + 1) := by
      have entry := bounded k
      omega
    exact add_envelope _ _ _ _ _ localBound tail
  | pop k value next ih =>
    have tail := ih (value store (slots k).head?) (Function.update slots k (slots k).tail)
      bound (updated_pop_bound slots bound bounded k)
    have localBound : (slots k).length + (slots k).tail.length + 2 ≤
        2 * (bound + pushes next + 1) := by
      have entry := bounded k
      simp only [List.length_tail]
      omega
    exact add_envelope _ _ _ _ _ localBound tail
  | load value next ih => exact ih (value store) slots bound bounded
  | branch test yes no ihYes ihNo =>
    cases choice : test store
    · change (if test store then clock yes store slots else clock no store slots) ≤ _
      rw [choice]
      exact (ihNo store slots bound bounded).trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.le_max_right _ _))
          (Nat.add_le_add_right (Nat.add_le_add_left (Nat.le_max_right _ _) bound) 1))
    · change (if test store then clock yes store slots else clock no store slots) ≤ _
      rw [choice]
      exact (ihYes store slots bound bounded).trans
        (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.le_max_left _ _))
          (Nat.add_le_add_right (Nat.add_le_add_left (Nat.le_max_left _ _) bound) 1))
  | goto label => simp only [clock, actions, Nat.mul_zero, Nat.zero_mul, Nat.le_refl]
  | halt => simp only [clock, actions, Nat.mul_zero, Nat.zero_mul, Nat.le_refl]

theorem actual_path_bound (machine : Λ → TM2.Stmt Γ Λ σ) (statement : TM2.Stmt Γ Λ σ)
    (store : σ) (slots : ∀ k, List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((slots k).map some).reverse)
    (bound : Nat) (bounded : ∀ k, (slots k).length ≤ bound) :
    ∃ (changed : ListBlank (∀ k, Option (Γ k)))
      (trace : List (ScannerPaths.State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ))),
      (∀ k, changed.map (proj k) = ListBlank.mk (((TM2.stepAux statement store slots).stk k).map some).reverse) ∧
      trace.head? = some (TM1.stepAux (TM2to1.trNormal statement) store (ScannerPaths.baseTape tracks)) ∧
      trace.IsChain (fun before after => TM1.step (TM2to1.tr machine) before = some after) ∧
      trace.getLast? = some (representedFinal statement store slots changed) ∧
      trace.length ≤ 2 * actions statement * (bound + pushes statement + 1) + 1 := by
  obtain ⟨changed, trace, changedRep, first, chain, last, length⟩ :=
    statement_path machine statement store slots tracks represented
  refine ⟨changed, trace, changedRep, first, chain, last, ?_⟩
  rw [length]
  exact Nat.add_le_add_right (clock_bound statement store slots bound bounded) 1

end PaperProofs.Common.Native.PSTRWordBool.ScannerClock
