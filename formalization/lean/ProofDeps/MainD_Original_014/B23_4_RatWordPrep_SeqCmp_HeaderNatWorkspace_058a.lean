module

public import B23_4_RatWordPrep_SeqCmp_HeaderNatRun_054

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.HeaderNat

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool

variable {C : Type*}

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) .halt point) ≤ 16 := by
  cases point with
  | header point => fin_cases point <;> exact of_decide_eq_true rfl
  | field point => fin_cases point <;> exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem step_bound (before after : State C) (bound : Nat)
    (edge : TM2.step (program .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length ≤ bound) :
    ∀ slot,(after.stk slot).length ≤ bound+16 := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact fun slot => (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
        (Nat.add_le_add_left (program_pushes point) bound)

theorem trace_bound (run : List (State C)) (before : State C) (bound : Nat)
    (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (program .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length ≤ bound) :
    ∀ current∈run,∀ slot,(current.stk slot).length ≤ bound+16*run.length := by
  induction run generalizing before bound with
  | nil => simp
  | cons firstState rest ih =>
    have same : firstState=before := Option.some.inj first
    subst firstState
    cases rest with
    | nil =>
      intro current member slot
      have same:=List.mem_singleton.mp member
      subst current
      exact (bounded slot).trans (Nat.le_add_right _ _)
    | cons next rest =>
      obtain ⟨edge,later⟩:=List.isChain_cons_cons.mp chain
      have step:=step_bound before next bound edge bounded
      intro current member slot
      rcases List.mem_cons.mp member with rfl | present
      · exact (bounded slot).trans (Nat.le_add_right _ _)
      · have tail:=ih next (bound+16) rfl later step current present slot
        simp only [List.length_cons] at tail ⊢
        omega

end B23_4_RatWordPrep.HeaderNat
