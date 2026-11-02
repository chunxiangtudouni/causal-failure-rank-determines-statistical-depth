module

public import Common.PSTR_WordBool_StackGeometry_013

/-! Actual internal stack snapshots of a TM2 statement. The syntax-derived
push allowance bounds every intermediate snapshot, including branches chosen
by the real store. No intermediate-workspace premise is supplied by a caller. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.AuxWorkspace

open Turing

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

abbrev Slots := ∀ k, List (Γ k)
abbrev Snapshot := σ × Slots (Γ := Γ)

def pushes : TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => pushes next + 1
  | .peek _ _ next | .pop _ _ next | .load _ next => pushes next
  | .branch _ yes no => max (pushes yes) (pushes no)
  | .goto _ | .halt => 0

def nodes : TM2.Stmt Γ Λ σ → σ → Slots (Γ := Γ) → List (Snapshot (Γ := Γ) (σ := σ))
  | .push k value next, store, slots =>
      (store, slots) :: nodes next store (Function.update slots k (value store :: slots k))
  | .peek k value next, store, slots =>
      (store, slots) :: nodes next (value store (slots k).head?) slots
  | .pop k value next, store, slots =>
      (store, slots) :: nodes next (value store (slots k).head?) (Function.update slots k (slots k).tail)
  | .load value next, store, slots => (store, slots) :: nodes next (value store) slots
  | .branch test yes no, store, slots =>
      (store, slots) :: if test store then nodes yes store slots else nodes no store slots
  | .goto _, store, slots | .halt, store, slots => [(store, slots)]

theorem updated_push_bound (store : σ) (slots : Slots (Γ := Γ)) (bound : Nat)
    (bounded : ∀ k, (slots k).length ≤ bound) (k : K) (value : σ → Γ k) :
    ∀ other, ((Function.update slots k (value store :: slots k)) other).length ≤ bound + 1 := by
  intro other
  by_cases same : other = k
  · subst other
    simpa only [Function.update_self, List.length_cons] using Nat.add_le_add_right (bounded k) 1
  · rw [Function.update_of_ne same]
    exact (bounded other).trans (Nat.le_succ bound)

theorem updated_pop_bound (slots : Slots (Γ := Γ)) (bound : Nat)
    (bounded : ∀ k, (slots k).length ≤ bound) (k : K) :
    ∀ other, ((Function.update slots k (slots k).tail) other).length ≤ bound := by
  intro other
  by_cases same : other = k
  · subst other
    rw [Function.update_self]
    simpa only [List.length_tail] using (Nat.sub_le (slots k).length 1).trans (bounded k)
  · rw [Function.update_of_ne same]
    exact bounded other

theorem endpoint_mem (statement : TM2.Stmt Γ Λ σ) (store : σ) (slots : Slots (Γ := Γ)) :
    ((TM2.stepAux statement store slots).var, (TM2.stepAux statement store slots).stk) ∈
      nodes statement store slots := by
  induction statement generalizing store slots with
  | push k value next ih => exact List.mem_cons_of_mem _ (ih _ _)
  | peek k value next ih => exact List.mem_cons_of_mem _ (ih _ _)
  | pop k value next ih => exact List.mem_cons_of_mem _ (ih _ _)
  | load value next ih => exact List.mem_cons_of_mem _ (ih _ _)
  | branch test yes no ihYes ihNo =>
    cases choice : test store
    · simpa only [TM2.stepAux, nodes, choice, Bool.cond_false, Bool.false_eq_true, ite_false]
        using List.mem_cons_of_mem (store, slots) (ihNo store slots)
    · simpa only [TM2.stepAux, nodes, choice, Bool.cond_true, ite_true]
        using List.mem_cons_of_mem (store, slots) (ihYes store slots)
  | goto label => exact List.mem_singleton_self _
  | halt => exact List.mem_singleton_self _

theorem node_bound (statement : TM2.Stmt Γ Λ σ) (store : σ) (slots : Slots (Γ := Γ))
    (bound : Nat) (bounded : ∀ k, (slots k).length ≤ bound) :
    ∀ snapshot ∈ nodes statement store slots, ∀ k,
      (snapshot.2 k).length ≤ bound + pushes statement := by
  induction statement generalizing store slots bound with
  | push k value next ih =>
    intro snapshot present other
    rcases List.mem_cons.mp present with same | later
    · subst snapshot
      exact (bounded other).trans (Nat.le_add_right _ _)
    · have result := ih store (Function.update slots k (value store :: slots k)) (bound + 1)
        (updated_push_bound store slots bound bounded k value) snapshot later other
      simpa only [pushes, Nat.add_assoc, Nat.add_comm 1] using result
  | peek k value next ih =>
    intro snapshot present other
    rcases List.mem_cons.mp present with same | later
    · subst snapshot
      exact (bounded other).trans (Nat.le_add_right _ _)
    · exact ih _ slots bound bounded snapshot later other
  | pop k value next ih =>
    intro snapshot present other
    rcases List.mem_cons.mp present with same | later
    · subst snapshot
      exact (bounded other).trans (Nat.le_add_right _ _)
    · exact ih _ _ bound (updated_pop_bound slots bound bounded k) snapshot later other
  | load value next ih =>
    intro snapshot present other
    rcases List.mem_cons.mp present with same | later
    · subst snapshot
      exact (bounded other).trans (Nat.le_add_right _ _)
    · exact ih _ slots bound bounded snapshot later other
  | branch test yes no ihYes ihNo =>
    intro snapshot present other
    rcases List.mem_cons.mp present with same | later
    · subst snapshot
      exact (bounded other).trans (Nat.le_add_right _ _)
    · cases choice : test store
      · simp only [choice, Bool.false_eq_true, ite_false] at later
        exact (ihNo store slots bound bounded snapshot later other).trans
          (Nat.add_le_add_left (Nat.le_max_right _ _) bound)
      · simp only [choice, ite_true] at later
        exact (ihYes store slots bound bounded snapshot later other).trans
          (Nat.add_le_add_left (Nat.le_max_left _ _) bound)
  | goto label =>
    intro snapshot present other
    have same := List.mem_singleton.mp present
    subst snapshot
    exact bounded other
  | halt =>
    intro snapshot present other
    have same := List.mem_singleton.mp present
    subst snapshot
    exact bounded other

theorem endpoint_bound (statement : TM2.Stmt Γ Λ σ) (store : σ) (slots : Slots (Γ := Γ))
    (bound : Nat) (bounded : ∀ k, (slots k).length ≤ bound) (k : K) :
    ((TM2.stepAux statement store slots).stk k).length ≤ bound + pushes statement :=
  node_bound statement store slots bound bounded _ (endpoint_mem statement store slots) k

end PaperProofs.Common.Native.PSTRWordBool.AuxWorkspace
