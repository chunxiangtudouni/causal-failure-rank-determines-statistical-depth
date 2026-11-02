module

public import B23_4_RatWordPrep_SeqCmp_WordResourceTransport_140

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool

variable {σ Λ : Type*}

theorem update_mass (slots : RatInput.Stack → List Bool) (slot : RatInput.Stack) (cells : List Bool) :
    RatInput.occupied (Function.update slots slot cells)+(slots slot).length=
      RatInput.occupied slots+cells.length := by
  fin_cases slot <;> simp [RatInput.occupied,Function.update,Fin.sum_univ_succ] <;> omega

theorem push_mass (slots : RatInput.Stack → List Bool) (slot : RatInput.Stack) (bit : Bool) :
    RatInput.occupied (Function.update slots slot (bit::slots slot))=RatInput.occupied slots+1 := by
  have count := update_mass slots slot (bit::slots slot)
  simp only [List.length_cons] at count
  omega

theorem pop_mass (slots : RatInput.Stack → List Bool) (slot : RatInput.Stack) :
    RatInput.occupied (Function.update slots slot (slots slot).tail)≤RatInput.occupied slots := by
  have count := update_mass slots slot (slots slot).tail
  rw [List.length_tail] at count
  omega

/-- Total physical mass grows by actual pushes, not by a multiplicative
per-stack envelope. This is uniform for the finite source and all stores. -/
theorem node_mass (body : TM2.Stmt RatInput.Alphabet Λ σ) (memory : σ)
    (slots : RatInput.Stack → List Bool) :
    ∀ node∈AuxWorkspace.nodes body memory slots,
      RatInput.occupied node.2≤RatInput.occupied slots+AuxWorkspace.pushes body := by
  induction body generalizing memory slots with
  | push slot value tail ih =>
    intro node member
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_add_right _ _
    · have bound := ih memory (Function.update slots slot (value memory::slots slot)) node later
      rw [push_mass] at bound
      change RatInput.occupied node.2≤RatInput.occupied slots+(AuxWorkspace.pushes tail+1)
      omega
  | peek slot value tail ih =>
    intro node member
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_add_right _ _
    · exact ih (value memory (slots slot).head?) slots node later
  | pop slot value tail ih =>
    intro node member
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_add_right _ _
    · exact (ih (value memory (slots slot).head?) (Function.update slots slot (slots slot).tail) node later).trans
        (Nat.add_le_add_right (pop_mass slots slot) _)
  | load value tail ih =>
    intro node member
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_add_right _ _
    · exact ih (value memory) slots node later
  | branch test yes no yesBound noBound =>
    intro node member
    cases selected : test memory with
    | false =>
      simp only [AuxWorkspace.nodes,selected,Bool.false_eq_true,ite_false] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_add_right _ _
      · exact (noBound memory slots node later).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
    | true =>
      simp only [AuxWorkspace.nodes,selected,ite_true] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_add_right _ _
      · exact (yesBound memory slots node later).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto target | halt =>
    intro node member
    have same := List.mem_singleton.mp member
    subst node
    exact Nat.le_refl _

theorem step_mass {source : Λ → TM2.Stmt RatInput.Alphabet Λ σ} (cap : Nat)
    (pushes : ∀ point,AuxWorkspace.pushes (source point)≤cap)
    (before after : TM2.Cfg RatInput.Alphabet Λ σ) (edge : TM2.step source before=some after) :
    RatInput.occupied after.stk≤RatInput.occupied before.stk+cap := by
  cases before with
  | mk position memory slots =>
    cases position with
    | none => cases edge
    | some point =>
      have equal : after=TM2.stepAux (source point) memory slots := (Option.some.inj edge).symm
      subst after
      exact (node_mass (source point) memory slots _ (AuxWorkspace.endpoint_mem _ _ _)).trans
        (Nat.add_le_add_left (pushes point) _)

theorem trace_mass {source : Λ → TM2.Stmt RatInput.Alphabet Λ σ} (cap : Nat)
    (pushes : ∀ point,AuxWorkspace.pushes (source point)≤cap)
    (trace : List (TM2.Cfg RatInput.Alphabet Λ σ)) (before : TM2.Cfg RatInput.Alphabet Λ σ)
    (bound : Nat) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step source a=some b)) (initial : RatInput.occupied before.stk≤bound) :
    ∀ current∈trace,RatInput.occupied current.stk≤bound+cap*trace.length := by
  induction trace generalizing before bound with
  | nil => simp
  | cons start rest ih =>
    have equal : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have equal := List.mem_singleton.mp member
      subst current
      exact initial.trans (Nat.le_add_right _ _)
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have nextMass := (step_mass cap pushes before next edge).trans (Nat.add_le_add_right initial cap)
      intro current member
      rcases List.mem_cons.mp member with rfl | later
      · exact initial.trans (Nat.le_add_right _ _)
      · have tail := ih next (bound+cap) rfl tailChain nextMass current later
        simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at tail ⊢
        omega

end B23_4_RatWordPrep.WordFinish.Resources
