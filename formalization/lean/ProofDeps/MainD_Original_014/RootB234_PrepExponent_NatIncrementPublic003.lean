module

public import RootB234_PrepExponent_NatIncrementResources002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.NatIncrement
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
variable {C : Type*}

theorem restore_proper (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (source temporary : List Bool) :
    ∀ current ∈ (restoreTrace background context memory source temporary).dropLast,current.l=some 3 := by
  induction temporary generalizing memory source with
  | nil => intro current member; simp [restoreTrace] at member; subst current; rfl
  | cons bit later ih =>
      intro current member
      rw [restoreTrace,List.dropLast_cons_of_ne_nil (restore_nonempty _ _ _ _ _)] at member
      rcases List.mem_cons.mp member with rfl | rest
      · rfl
      · exact ih _ _ current rest

theorem actual_proper (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (digits tail temporary : List Bool) :
    ∀ current ∈ (actualTrace background context memory digits tail temporary).dropLast,
      current.l=some 0 ∨ current.l=some 3 := by
  induction digits generalizing memory temporary with
  | nil =>
      intro current member
      rw [actualTrace,List.dropLast_cons_of_ne_nil (restore_nonempty _ _ _ _ _)] at member
      rcases List.mem_cons.mp member with rfl | rest
      · exact Or.inl rfl
      · exact Or.inr (restore_proper _ _ _ _ _ current rest)
  | cons bit later ih =>
      cases bit with
      | false =>
          intro current member
          rw [actualTrace,List.dropLast_cons_of_ne_nil (restore_nonempty _ _ _ _ _)] at member
          rcases List.mem_cons.mp member with rfl | rest
          · exact Or.inl rfl
          · exact Or.inr (restore_proper _ _ _ _ _ current rest)
      | true =>
          intro current member
          rw [actualTrace,List.dropLast_cons_of_ne_nil (actual_nonempty _ _ _ _ _ _)] at member
          rcases List.mem_cons.mp member with rfl | rest
          · exact Or.inl rfl
          · exact ih _ _ current rest

theorem caller_agrees (caller : Statement C) (point : Label) (active : point=0 ∨ point=3) :
    program caller point=program .halt point := by
  rcases active with rfl | rfl <;> rfl

theorem caller_clock (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (digits tail temporary : List Bool) (current : State C)
    (member : current ∈ (actualTrace background context memory digits tail temporary).dropLast)
    (point : Label) (selected : current.l=some point) :
    ScannerStatement.clock (program caller point) current.var current.stk=statementClock current := by
  have proper := actual_proper background context memory digits tail temporary current member
  have active : point=0 ∨ point=3 := by
    rcases proper with zero | three
    · exact Or.inl (Option.some.inj (selected.symm.trans zero))
    · exact Or.inr (Option.some.inj (selected.symm.trans three))
  rw [caller_agrees caller point active]
  simp only [statementClock,selected]

theorem actual_charged (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (tail : List Bool) :
    (actualTrace background context memory (PSTRTMNatValue017.rawPayload number) tail []).length+
      traceClockSum (actualTrace background context memory (PSTRTMNatValue017.rawPayload number) tail []) ≤
      435*(scale background number tail)^2 := by
  have time := actual_time background context memory number tail
  have clocks := actual_clock_sum background context memory number tail
  have positive : 1 ≤ scale background number tail := by simp [scale]
  have square : scale background number tail ≤ (scale background number tail)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (scale background number tail) positive
  omega

private theorem supports_stmt (body : Statement C) :
    TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports (caller : Statement C) : TM2.Supports (program caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => supports_stmt (program caller point)⟩

theorem finite_store [Finite C] : Finite (Store C) := inferInstance

namespace Public
theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (source : Label → Statement C) (support : Finset Label),
      source=program .halt ∧ support=Finset.univ ∧ TM2.Supports source support :=
  ⟨program .halt,Finset.univ,rfl,rfl,supports .halt⟩
end Public
end RootB234.PrepExponent.NatIncrement
