module

public import PSTR_WordBool_RatPair_Serialize_Run_002

/-! Fixed syntax bounds and the same physical trace resource propagation.
No enclosing runtime is a resource parameter of this serializer. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer

open Turing PSTRWordVM RationalControllerComputation
open scoped BigOperators

variable {C : Type*}

def Work2 (slot : RatInput.Stack) : Prop := RatInput.Encoder.Work slot ∨ slot=8 ∨ slot=9

instance (slot : RatInput.Stack) : Decidable (Work2 slot) := by unfold Work2;infer_instance

def writesDecidable2 : (body : Statement C) → Decidable (StackIso.WritesOnly Work2 body)
  | .push slot _ tail | .pop slot _ tail => by
    change Decidable (Work2 slot ∧ StackIso.WritesOnly Work2 tail)
    letI := writesDecidable2 tail
    infer_instance
  | .peek _ _ tail | .load _ tail => writesDecidable2 tail
  | .branch _ yes no => by
    change Decidable (StackIso.WritesOnly Work2 yes ∧ StackIso.WritesOnly Work2 no)
    letI := writesDecidable2 yes
    letI := writesDecidable2 no
    infer_instance
  | .goto _ | .halt => isTrue trivial

local instance (body : Statement C) : Decidable (StackIso.WritesOnly Work2 body) := writesDecidable2 body

theorem program_actions2 (point : Label) : ScannerClock.actions (program2 (C:=C) .halt point) ≤ 32 := by
  cases point with
  | boot which => cases which <;> exact of_decide_eq_true rfl
  | phase which old =>
    cases which <;> cases old <;> first
    | exact of_decide_eq_true rfl
    | (rename_i small; fin_cases small <;> exact of_decide_eq_true rfl)
  | trim which => cases which <;> exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_pushes2 (point : Label) : AuxWorkspace.pushes (program2 (C:=C) .halt point) ≤ 32 := by
  cases point with
  | boot which => cases which <;> exact of_decide_eq_true rfl
  | phase which old =>
    cases which <;> cases old <;> first
    | exact of_decide_eq_true rfl
    | (rename_i small; fin_cases small <;> exact of_decide_eq_true rfl)
  | trim which => cases which <;> exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem program_writes2 (point : Label) : StackIso.WritesOnly Work2 (program2 (C:=C) .halt point) := by
  cases point with
  | boot which => cases which <;> exact of_decide_eq_true rfl
  | phase which old =>
    cases which <;> cases old <;> first
    | exact of_decide_eq_true rfl
    | (rename_i small; fin_cases small <;> exact of_decide_eq_true rfl)
  | trim which => cases which <;> exact of_decide_eq_true rfl
  | done => exact of_decide_eq_true rfl

theorem step_resources2 (before after : State C) (bound : Nat)
    (edge : TM2.step (program2 .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    (∀ slot,(after.stk slot).length≤bound+32) ∧
      ∀ slot,¬Work2 slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have equal : after=TM2.stepAux (program2 .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      refine ⟨?_,?_⟩
      · intro slot
        exact (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
          (Nat.add_le_add_left (program_pushes2 point) bound)
      · intro slot untouched
        exact StackIso.nodes_frame Work2 _ (program_writes2 point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_resources2 (trace : List (State C)) (before : State C)
    (background : RatInput.Stack→List Bool) (bound : Nat)
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b=>TM2.step (program2 .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound)
    (frames : ∀ slot,¬Work2 slot→before.stk slot=background slot) :
    ∀ current∈trace,
      (∀ slot,(current.stk slot).length≤bound+32*trace.length) ∧
      ∀ slot,¬Work2 slot→current.stk slot=background slot := by
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
      have step:=step_resources2 before next bound edge bounded
      have nextFrames : ∀ slot,¬Work2 slot→next.stk slot=background slot :=
        fun slot untouched=>(step.2 slot untouched).trans (frames slot untouched)
      intro current member
      rcases List.mem_cons.mp member with same|later
      · subst current
        exact ⟨fun slot=>(bounded slot).trans (Nat.le_add_right _ _),frames⟩
      · have tail:=ih next (bound+32) rfl tailChain step.1 nextFrames current later
        refine ⟨?_,tail.2⟩
        intro slot
        have perSlot:=tail.1 slot
        simp only [List.length_cons] at perSlot ⊢
        omega

theorem internal_resources2 (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program2 .halt point) current.var current.stk,
      (∀ slot,(node.2 slot).length≤bound+32) ∧
        ∀ slot,¬Work2 slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program2 .halt point) current.var current.stk≤64*(bound+33) := by
  refine ⟨?_,?_⟩
  · intro node member
    refine ⟨?_,?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes2 point) bound)
    · intro slot untouched
      exact StackIso.nodes_frame Work2 _ (program_writes2 point) current.var current.stk slot untouched node member
  · have clock:=ScannerClock.clock_bound (program2 .halt point) current.var current.stk bound bounded
    exact clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions2 point))
      (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes2 point) bound) 1))

def outside2 (background : RatInput.Stack → List Bool) : Nat :=
  ∑ slot, if Work2 slot then 0 else (background slot).length

theorem occupied_bank2 (background : RatInput.Stack → List Bool)
    (xNum xDen yNum yDen numerator denominator raw left counter : List Bool) :
    RatInput.occupied (bank background xNum xDen yNum yDen numerator denominator raw left counter) =
      outside2 background+(background 7).length+(background 15).length+
        xNum.length+xDen.length+yNum.length+yDen.length+numerator.length+denominator.length+
        raw.length+left.length+counter.length := by
  simp [RatInput.occupied,bank,outside2,Work2,RatInput.Encoder.Work,Fin.sum_univ_succ,Nat.add_assoc]
  omega

theorem bank_frame2 (background : RatInput.Stack → List Bool)
    (xNum xDen yNum yDen numerator denominator raw left counter : List Bool)
    (slot : RatInput.Stack) (untouched : ¬Work2 slot) :
    bank background xNum xDen yNum yDen numerator denominator raw left counter slot = background slot := by
  simp only [Work2,RatInput.Encoder.Work,not_or] at untouched
  rcases untouched with ⟨⟨n3,n4,n5,n6,_n7,n12,n13,n14,_n15⟩,n8,n9⟩
  simp only [bank,n3,n4,n5,n6,n8,n9,n12,n13,n14,ite_false]

theorem program_proper2 (caller : Statement C) (point : Label) (proper : point ≠ .done) :
    program2 caller point = program2 .halt point := by
  cases point with
  | boot which => cases which <;> rfl
  | phase which old => rfl
  | trim which => cases which <;> rfl
  | done => exact False.elim (proper rfl)

theorem chain_caller2 (caller : Statement C) (trace : List (State C))
    (chain : trace.IsChain (fun a b => TM2.step (program2 .halt) a = some b))
    (proper : ∀ current∈trace.dropLast, current.l ≠ some .done) :
    trace.IsChain (fun a b => TM2.step (program2 caller) a = some b) := by
  induction trace with
  | nil => exact List.isChain_nil
  | cons before rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      refine List.isChain_cons_cons.mpr ⟨?_,ih tailChain ?_⟩
      · have beforeProper := proper before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self)
        cases before with
        | mk position memory contents =>
          cases position with
          | none => cases edge
          | some point =>
            have notDone : point ≠ .done := by intro same;subst point;exact beforeProper rfl
            change some (TM2.stepAux (program2 caller point) memory contents) = some next
            rw [program_proper2 caller point notDone]
            exact edge
      · intro current member
        apply proper current
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ member

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer
