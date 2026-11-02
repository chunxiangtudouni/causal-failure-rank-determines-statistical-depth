module

public import Common.PSTR_WordBool_RatInputSyntax_091

/-! The encoder is a bounded single pass over the two finite fields.
Substituting its explicit 8*(NUMbits+DENbits)+34 bound gives linear local
workspace in those fields, independent of the enclosing controller time. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder

open Turing PSTRWordVM RationalControllerComputation
open scoped BigOperators

variable {C : Type*}

theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step (program .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    (∀ slot,(after.stk slot).length≤bound+15) ∧
      ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have equal : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      refine ⟨?_,?_⟩
      · intro slot
        exact (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
          (Nat.add_le_add_left (program_pushes point) bound)
      · intro slot untouched
        exact StackIso.nodes_frame Work _ (program_writes point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_resources (trace : List (State C)) (before : State C)
    (background : RatInput.Stack→List Bool) (bound : Nat)
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (program .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound)
    (frames : ∀ slot,¬Work slot→before.stk slot=background slot) :
    ∀ current∈trace,
      (∀ slot,(current.stk slot).length≤bound+15*trace.length) ∧
      ∀ slot,¬Work slot→current.stk slot=background slot := by
  induction trace generalizing before bound with
  | nil => simp
  | cons firstState rest ih =>
    have equal : firstState=before:=Option.some.inj first
    subst firstState
    cases rest with
    | nil =>
      intro current member
      have same:=List.mem_singleton.mp member
      subst current
      refine ⟨?_,frames⟩
      intro slot
      exact (bounded slot).trans (by simp)
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      have step:=step_resources before next bound edge bounded
      have nextFrames : ∀ slot,¬Work slot→next.stk slot=background slot :=
        fun slot untouched=>(step.2 slot untouched).trans (frames slot untouched)
      intro current member
      rcases List.mem_cons.mp member with same|later
      · subst current
        exact ⟨fun slot=>(bounded slot).trans (Nat.le_add_right _ _),frames⟩
      · have tail:=ih next (bound+15) rfl tailChain step.1 nextFrames current later
        refine ⟨?_,tail.2⟩
        intro slot
        have perSlot:=tail.1 slot
        simp only [List.length_cons] at perSlot ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      (∀ slot,(node.2 slot).length≤bound+15) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk≤30*(bound+16) := by
  refine ⟨?_,?_⟩
  · intro node member
    refine ⟨?_,?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound)
    · intro slot untouched
      exact StackIso.nodes_frame Work _ (program_writes point) current.var current.stk slot untouched node member
  · have clock:=ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded
    exact clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
      (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))

theorem occupied_bound (contents : RatInput.Stack→List Bool) (bound : Nat)
    (bounded : ∀ slot,(contents slot).length≤bound) : RatInput.occupied contents≤16*bound := by
  calc
    RatInput.occupied contents≤∑ _slot : RatInput.Stack,bound:=Finset.sum_le_sum (fun slot _=>bounded slot)
    _=16*bound:=by simp

theorem point_mass (contents : RatInput.Stack→List Bool) (slot : RatInput.Stack) :
    (contents slot).length≤RatInput.occupied contents := by
  exact Finset.single_le_sum (fun other _=>Nat.zero_le (contents other).length) (Finset.mem_univ slot)

def outside (background : RatInput.Stack→List Bool) : Nat :=
  ∑ slot,if Work slot then 0 else (background slot).length

theorem occupied_bank (background : RatInput.Stack→List Bool)
    (source scratch numRev denRev numerator denominator raw left counter : List Bool) :
    RatInput.occupied (bank background source scratch numRev denRev numerator denominator raw left counter)=
      outside background+source.length+scratch.length+numRev.length+denRev.length+
        numerator.length+denominator.length+raw.length+left.length+counter.length := by
  simp [RatInput.occupied,bank,outside,Work,Fin.sum_univ_succ,Nat.add_assoc]
  omega

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder
