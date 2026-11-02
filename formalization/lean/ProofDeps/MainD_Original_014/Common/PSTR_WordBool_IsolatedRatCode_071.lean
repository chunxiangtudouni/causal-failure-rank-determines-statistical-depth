module

public import Common.PSTR_WordVM_VirtualBool_025
public import Common.PSTR_WordVM_StackIso_042
public import Common.PSTR_WordBool_NativeMulCode_057

/-! The actual isolated original-codec arithmetic caller. Code roles0/1
are fixed to physical13/14. Initialization is a paid load at1, native body
is0, and2 is the active, unexecuted caller. No physical stack is swapped. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.IsolatedRat

open Turing PSTRWordVM

abbrev Stack := Fin 16
abbrev Label := Fin 3
abbrev Alphabet (_ : Stack) := Bool
abbrev Store (C : Type*) (states : Nat) := C × BoolOnStacks.Store states
abbrev Statement (C : Type*) (states : Nat) := TM2.Stmt Alphabet Label (Store C states)
abbrev State (C : Type*) (states : Nat) := TM2.Cfg Alphabet Label (Store C states)

variable {C : Type*} {states : Nat}

def roles : Stack ≃ Stack := (Equiv.swap 0 13).trans (Equiv.swap 1 14)

def port (point : VirtualReturn.Label) : Label := if point = 0 then 0 else 2

def body (machine : TM0.Machine Bool (Fin (states + 1))) : Statement C states :=
  LabelMap.statement port (StackIso.statement roles
    (VirtualReturn.statement (C := C) (VirtualBool.source machine ())))

def program (machine : TM0.Machine Bool (Fin (states + 1)))
    (caller : Statement C states) (point : Label) : Statement C states :=
  if point = 0 then body machine else if point = 1 then
    .load (fun memory => (memory.1, default)) (.goto (fun _ => 0)) else caller

def configuration (before : VirtualReturn.State C (BoolOnStacks.Store states)) : State C states :=
  LabelMap.configuration port (StackIso.configuration roles before)

def cells (background : Stack → List Bool) (right left : List Bool) : Stack → List Bool :=
  fun point => if point = 13 then right else if point = 14 then left else background point

def entry (context : C) (memory : BoolOnStacks.Store states)
    (background : Stack → List Bool) (input : List Bool) : State C states :=
  ⟨some 1, (context, memory), cells background input []⟩

def pulled (background : Stack → List Bool) : Stack → List Bool := fun point => background (roles point)

def original (context : C) (background : Stack → List Bool) (input : List Bool) :
    VirtualReturn.State C (BoolOnStacks.Store states) :=
  VirtualReturn.configuration context (pulled background)
    (TM2.init (Γ := PushPop.Alphabet) (Λ := Unit) (σ := BoolOnStacks.Store states) 0 input)

def outside (background : Stack → List Bool) : Nat := VirtualReturn.outside (pulled background)

def occupied (contents : Stack → List Bool) : Nat := ∑ point, (contents point).length

def represented (before : State C states) : TM0.Cfg Bool (Fin (states + 1)) :=
  ⟨before.var.2.1, Tape.mk' (ListBlank.mk (before.stk 14)) (ListBlank.mk (before.stk 13))⟩

theorem represented_configuration (before : VirtualReturn.State C (BoolOnStacks.Store states)) :
    represented (configuration before) = VirtualBool.representedState before := rfl

theorem occupied_eq (contents : Stack → List Bool) : occupied contents = VirtualReturn.occupiedSlots contents := by
  simp [occupied, Fin.sum_univ_succ, VirtualReturn.occupiedSlots, Nat.add_assoc]

theorem occupied_configuration (before : VirtualReturn.State C (BoolOnStacks.Store states)) :
    occupied (configuration before).stk = VirtualReturn.occupiedSlots before.stk := by
  change occupied (StackIso.slots roles before.stk) = _
  rw [occupied, StackIso.occupied_sum, ← occupied, occupied_eq]

theorem original_cells (context : C) (background : Stack → List Bool) (input : List Bool) :
    (configuration (original (states := states) context background input)).stk = cells background input [] := by
  funext point
  fin_cases point <;> rfl

theorem enter_step (machine : TM0.Machine Bool (Fin (states + 1))) (caller : Statement C states)
    (context : C) (memory : BoolOnStacks.Store states) (background : Stack → List Bool) (input : List Bool) :
    TM2.step (program machine caller) (entry context memory background input) =
      some (configuration (original context background input)) := by
  have same := original_cells (states := states) context background input
  change some (⟨some 0, (context, default), cells background input []⟩ : State C states) = _
  rw [← same]
  rfl

theorem body_actions (machine : TM0.Machine Bool (Fin (states + 1))) :
    ScannerClock.actions (body (C := C) machine) = 4 := by
  rw [body, LabelMap.statement_actions, StackIso.statement_actions]
  exact VirtualBool.actions machine

theorem body_pushes (machine : TM0.Machine Bool (Fin (states + 1))) :
    AuxWorkspace.pushes (body (C := C) machine) = 2 := by
  rw [body, LabelMap.statement_pushes, StackIso.statement_pushes]
  exact VirtualBool.pushes machine

theorem program_actions (machine : TM0.Machine Bool (Fin (states + 1))) (caller : Statement C states)
    (point : Label) (proper : point ≠ 2) : ScannerClock.actions (program machine caller point) ≤ 4 := by
  fin_cases point
  · exact (body_actions machine).le
  · exact Nat.zero_le _
  · exact False.elim (proper rfl)

theorem program_pushes (machine : TM0.Machine Bool (Fin (states + 1))) (caller : Statement C states)
    (point : Label) (proper : point ≠ 2) : AuxWorkspace.pushes (program machine caller point) ≤ 2 := by
  fin_cases point
  · exact (body_pushes machine).le
  · exact Nat.zero_le _
  · exact False.elim (proper rfl)

theorem core_writes (code : VirtualReturn.SmallStatement (BoolOnStacks.Store states)) :
    StackIso.WritesOnly (fun point : Stack => point = 13 ∨ point = 14)
      (StackIso.statement roles (VirtualReturn.statement (C := C) code)) := by
  induction code with
  | push point value tail ih | pop point value tail ih =>
    fin_cases point
    · exact ⟨Or.inl rfl, ih⟩
    · exact ⟨Or.inr rfl, ih⟩
  | peek point value tail ih | load value tail ih => exact ih
  | branch test yes no ihYes ihNo => exact ⟨ihYes, ihNo⟩
  | goto target | halt => trivial

theorem program_writes (machine : TM0.Machine Bool (Fin (states + 1))) (caller : Statement C states)
    (point : Label) (proper : point ≠ 2) :
    StackIso.WritesOnly (fun slot : Stack => slot = 13 ∨ slot = 14) (program machine caller point) := by
  fin_cases point
  · change StackIso.WritesOnly _ (LabelMap.statement port _)
    rw [StackIso.writes_labelMap]
    exact core_writes _
  · trivial
  · exact False.elim (proper rfl)

theorem internal_bound (machine : TM0.Machine Bool (Fin (states + 1))) (caller : Statement C states)
    (current : State C states) (point : Label) (proper : point ≠ 2) (K : Nat)
    (mass : occupied current.stk ≤ K) :
    (∀ node ∈ AuxWorkspace.nodes (program machine caller point) current.var current.stk,
      (∀ slot, (node.2 slot).length ≤ K + 2) ∧
      ∀ slot, slot ≠ 13 → slot ≠ 14 → node.2 slot = current.stk slot) ∧
    ScannerStatement.clock (program machine caller point) current.var current.stk ≤ 8 * (K + 3) := by
  have bounded : ∀ slot, (current.stk slot).length ≤ K := by
    intro slot
    exact (Finset.single_le_sum (f := fun other : Stack => (current.stk other).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ slot)).trans mass
  have pushes := program_pushes machine caller point proper
  refine ⟨?_, ?_⟩
  · intro node member
    refine ⟨?_, ?_⟩
    · intro slot
      exact (AuxWorkspace.node_bound _ _ _ K bounded node member slot).trans (by omega)
    · intro slot notR notL
      exact StackIso.nodes_frame _ _ (program_writes machine caller point proper) _ _ slot
        (by simp only [notR, notL, or_self, not_false_eq_true]) node member
  · have bound := ScannerClock.clock_bound (program machine caller point) current.var current.stk K bounded
    have actions := program_actions machine caller point proper
    exact bound.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 actions) (by omega))

end PaperProofs.Common.Native.PSTRWordBool.IsolatedRat
