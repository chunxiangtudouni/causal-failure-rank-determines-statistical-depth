module

public import Common.PSTR_WordBool_RatOutputNative_080

/-! Fixed-syntax internal resources of the joined actual native/output
program. Workspace comes from current data, independently of elapsed time.
The actual final caller is excluded, and archive1/unread0 are framed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatOutput.Link

open Turing PSTRWordVM

variable {C : Type*} {states : Nat}

theorem program_actions (machine : TM0.Machine Bool (Fin (states+1))) (caller : Statement C states)
    (point : Label) (proper : point ≠ 10) : ScannerClock.actions (program machine caller point) ≤ 8 := by
  by_cases native : point.val < 2
  · let old : IsolatedRat.Label := ⟨point.val,by omega⟩
    have equal : point = nativeLabel old := Fin.ext rfl
    have oldProper : old ≠ 2 := by intro same; have value := congrArg Fin.val same; dsimp [old] at value; omega
    rw [equal,program_native machine caller old oldProper,LabelMap.statement_actions,StoreIso.statement_actions]
    exact (IsolatedRat.program_actions machine .halt old oldProper).trans (by decide)
  · let old : RatOutput.Label := ⟨point.val-2,by have val := point.isLt; have different := proper; omega⟩
    have equal : point = readerLabel old := by apply Fin.ext; dsimp [readerLabel,old]; omega
    have oldProper : old ≠ 8 := by
      intro same
      have value := congrArg Fin.val same
      have current := point.isLt
      apply proper
      apply Fin.ext
      dsimp [old] at value
      omega
    rw [equal,program_reader machine caller old oldProper,LabelMap.statement_actions]
    exact RatOutput.program_actions .halt old oldProper

theorem program_pushes (machine : TM0.Machine Bool (Fin (states+1))) (caller : Statement C states)
    (point : Label) (proper : point ≠ 10) : AuxWorkspace.pushes (program machine caller point) ≤ 3 := by
  by_cases native : point.val < 2
  · let old : IsolatedRat.Label := ⟨point.val,by omega⟩
    have equal : point = nativeLabel old := Fin.ext rfl
    have oldProper : old ≠ 2 := by intro same; have value := congrArg Fin.val same; dsimp [old] at value; omega
    rw [equal,program_native machine caller old oldProper,LabelMap.statement_pushes,StoreIso.statement_pushes]
    exact (IsolatedRat.program_pushes machine .halt old oldProper).trans (by decide)
  · let old : RatOutput.Label := ⟨point.val-2,by have val := point.isLt; have different := proper; omega⟩
    have equal : point = readerLabel old := by apply Fin.ext; dsimp [readerLabel,old]; omega
    have oldProper : old ≠ 8 := by
      intro same
      have value := congrArg Fin.val same
      have current := point.isLt
      apply proper
      apply Fin.ext
      dsimp [old] at value
      omega
    rw [equal,program_reader machine caller old oldProper,LabelMap.statement_pushes]
    exact RatOutput.program_pushes .halt old oldProper

private theorem writes_store {σ τ Λ : Type*} (equivalence : σ ≃ τ) (allowed : RatOutput.Stack → Prop)
    (source : TM2.Stmt RatOutput.Alphabet Λ σ) :
    StackIso.WritesOnly allowed (StoreIso.statement equivalence source) ↔ StackIso.WritesOnly allowed source := by
  induction source with
  | push _ _ _ ih | pop _ _ _ ih => exact and_congr Iff.rfl ih
  | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact and_congr yes no
  | goto _ | halt => rfl

private theorem writes_mono {σ Λ : Type*} (source : TM2.Stmt RatOutput.Alphabet Λ σ)
    (old new : RatOutput.Stack → Prop) (included : ∀ point, old point → new point)
    (written : StackIso.WritesOnly old source) : StackIso.WritesOnly new source := by
  induction source with
  | push point _ _ ih | pop point _ _ ih => exact ⟨included point written.1,ih written.2⟩
  | peek _ _ _ ih | load _ _ ih => exact ih written
  | branch _ _ _ yes no => exact ⟨yes written.1,no written.2⟩
  | goto _ | halt => trivial

theorem program_writes (machine : TM0.Machine Bool (Fin (states+1))) (caller : Statement C states)
    (point : Label) (proper : point ≠ 10) :
    StackIso.WritesOnly (fun slot : RatOutput.Stack => slot = 13 ∨ slot = 14 ∨ slot = 7 ∨ slot = 15)
      (program machine caller point) := by
  by_cases native : point.val < 2
  · let old : IsolatedRat.Label := ⟨point.val,by omega⟩
    have equal : point = nativeLabel old := Fin.ext rfl
    have oldProper : old ≠ 2 := by intro same; have value := congrArg Fin.val same; dsimp [old] at value; omega
    rw [equal,program_native machine caller old oldProper,StackIso.writes_labelMap,writes_store]
    apply writes_mono _ (fun slot => slot=13 ∨ slot=14) _ _ (IsolatedRat.program_writes machine .halt old oldProper)
    intro slot selected
    rcases selected with atR | atL
    · exact Or.inl atR
    · exact Or.inr (Or.inl atL)
  · let old : RatOutput.Label := ⟨point.val-2,by have val := point.isLt; have different := proper; omega⟩
    have equal : point = readerLabel old := by apply Fin.ext; dsimp [readerLabel,old]; omega
    have oldProper : old ≠ 8 := by
      intro same
      have value := congrArg Fin.val same
      have current := point.isLt
      apply proper
      apply Fin.ext
      dsimp [old] at value
      omega
    rw [equal,program_reader machine caller old oldProper,StackIso.writes_labelMap]
    exact RatOutput.program_writes .halt old oldProper

theorem internal_bound (machine : TM0.Machine Bool (Fin (states+1))) (caller : Statement C states)
    (background : RatOutput.Stack → List Bool) (current : State C states) (K : Nat)
    (mass : RatOutput.occupied current.stk ≤ K)
    (frame : ∀ slot, slot ≠ 13 → slot ≠ 14 → slot ≠ 7 → slot ≠ 15 → current.stk slot = background slot)
    (point : Label) (proper : point ≠ 10) :
    (∀ node ∈ AuxWorkspace.nodes (program machine caller point) current.var current.stk,
      (∀ slot, (node.2 slot).length ≤ K+3) ∧
      ∀ slot, slot ≠ 13 → slot ≠ 14 → slot ≠ 7 → slot ≠ 15 → node.2 slot = background slot) ∧
    ScannerStatement.clock (program machine caller point) current.var current.stk ≤ 16*(K+4) := by
  have bounded : ∀ slot, (current.stk slot).length ≤ K := fun slot => (point_mass current.stk slot).trans mass
  have pushes := program_pushes machine caller point proper
  refine ⟨?_,?_⟩
  · intro node member
    refine ⟨?_,?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ K bounded node member slot).trans (by omega)
    · intro slot notR notL notC notT
      have unchanged := StackIso.nodes_frame _ _ (program_writes machine caller point proper) current.var current.stk slot
        (by simp only [notR,notL,notC,notT,or_self,not_false_eq_true]) node member
      exact unchanged.trans (frame slot notR notL notC notT)
  · have clock := ScannerClock.clock_bound (program machine caller point) current.var current.stk K bounded
    exact clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions machine caller point proper)) (by omega))

end PaperProofs.Common.Native.PSTRWordBool.RatOutput.Link
