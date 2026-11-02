module

public import PSTR_WordBool_RatBinary_Bank_003

/-! Fixed instruction syntax and all proper internal stack/clock bounds.
No operand field, budget or loop-time value appears in executable control. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatBinary

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*} {states : Nat}

theorem program_actions (machine : Machine states) (point : Label) :
    ScannerClock.actions (program (C:=C) machine .halt point)≤32 := by
  cases point with
  | pair point =>
    rw [program,LabelMap.statement_actions,StoreIso.statement_actions]
    exact RatPair.Link.program_actions point
  | arith point =>
    rw [program,LabelMap.statement_actions]
    by_cases done : point=10
    · subst point;exact Nat.zero_le _
    · exact (RatOutput.Link.program_actions machine .halt point done).trans (by decide)
  | drop point =>
    rw [program,LabelMap.statement_actions]
    exact (RatDrop.program_actions point).trans (by decide)
  | done => exact Nat.zero_le _

theorem program_pushes (machine : Machine states) (point : Label) :
    AuxWorkspace.pushes (program (C:=C) machine .halt point)≤32 := by
  cases point with
  | pair point =>
    rw [program,LabelMap.statement_pushes,StoreIso.statement_pushes]
    exact RatPair.Link.program_pushes point
  | arith point =>
    rw [program,LabelMap.statement_pushes]
    by_cases done : point=10
    · subst point;exact Nat.zero_le _
    · exact (RatOutput.Link.program_pushes machine .halt point done).trans (by decide)
  | drop point =>
    rw [program,LabelMap.statement_pushes]
    exact (RatDrop.program_pushes point).trans (by decide)
  | done => exact Nat.zero_le _

private theorem writes_store {σ τ Λ : Type*} (equivalence : σ≃τ) (allowed : RatInput.Stack→Prop)
    (body : TM2.Stmt RatInput.Alphabet Λ σ) :
    StackIso.WritesOnly allowed (StoreIso.statement equivalence body)↔StackIso.WritesOnly allowed body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih => exact and_congr Iff.rfl ih
  | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact and_congr yes no
  | goto _ | halt => rfl

private theorem writes_mono {σ Λ : Type*} (body : TM2.Stmt RatInput.Alphabet Λ σ)
    (old new : RatInput.Stack→Prop) (included : ∀ slot,old slot→new slot)
    (written : StackIso.WritesOnly old body) : StackIso.WritesOnly new body := by
  induction body with
  | push slot _ _ ih | pop slot _ _ ih => exact ⟨included slot written.1,ih written.2⟩
  | peek _ _ _ ih | load _ _ ih => exact ih written
  | branch _ _ _ yes no => exact ⟨yes written.1,no written.2⟩
  | goto _ | halt => trivial

theorem program_writes (machine : Machine states) (point : Label) :
    StackIso.WritesOnly RatPair.Link.Work (program (C:=C) machine .halt point) := by
  cases point with
  | pair point =>
    rw [program,StackIso.writes_labelMap,writes_store]
    exact RatPair.Link.program_writes point
  | arith point =>
    rw [program,StackIso.writes_labelMap]
    by_cases done : point=10
    · subst point;trivial
    · apply writes_mono _ (fun slot=>slot=13 ∨ slot=14 ∨ slot=7 ∨ slot=15) _ _
        (RatOutput.Link.program_writes machine .halt point done)
      intro slot owned
      rcases owned with rfl|rfl|rfl|rfl <;> simp [RatPair.Link.Work,RatInput.Encoder.Work]
  | drop point =>
    rw [program,StackIso.writes_labelMap]
    apply writes_mono _ (fun slot=>slot=15 ∨ slot=3) _ _ (RatDrop.program_writes point)
    intro slot owned
    rcases owned with rfl|rfl <;> simp [RatPair.Link.Work,RatInput.Encoder.Work]
  | done => trivial

theorem internal_bound (machine : Machine states) (background : RatInput.Stack→List Bool)
    (current : State C states) (bound : Nat)
    (mass : RatInput.occupied current.stk≤bound)
    (frame : ∀ slot,¬RatPair.Link.Work slot→current.stk slot=background slot) (point : Label) :
    (∀ node∈AuxWorkspace.nodes (program machine .halt point) current.var current.stk,
      (∀ slot,(node.2 slot).length≤bound+32) ∧
      ∀ slot,¬RatPair.Link.Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (program machine .halt point) current.var current.stk≤64*(bound+33) := by
  have bounded : ∀ slot,(current.stk slot).length≤bound:=
    fun slot=>(RatInput.Encoder.point_mass current.stk slot).trans mass
  refine ⟨?_,?_⟩
  · intro node member
    refine ⟨?_,?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes machine point) bound)
    · intro slot untouched
      exact (StackIso.nodes_frame _ _ (program_writes machine point) current.var current.stk slot untouched node member).trans
        (frame slot untouched)
  · exact (ScannerClock.clock_bound (program machine .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions machine point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes machine point) bound) 1))

end PaperProofs.Common.Native.PSTRWordBool.RatBinary
