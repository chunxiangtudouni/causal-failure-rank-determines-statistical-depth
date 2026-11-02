module

public import Common.PSTR_WordVM_BankTrace_005

/-! Compile-time transport of the SAME proved five-stack field trace.
Roles and labels are static code parameters; the actual UniqueStore
instances use constant Fin16 maps and fixed finite flags. No stacks are
moved between runs: translated push/pop instructions execute in place. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.FieldTransport

open Turing

abbrev Stack := Fin 16
abbrev Label := Fin 16
abbrev Alphabet (_ : Stack) := Bool
abbrev Store (Flags : Type*) := FieldCopy.Store × Flags
abbrev State (Flags : Type*) := TM2.Cfg Alphabet Label (Store Flags)
abbrev Statement (Flags : Type*) := TM2.Stmt Alphabet Label (Store Flags)

def slots (role : FieldCopy.Stack → Stack) (background : Stack → List Bool)
    (small : FieldCopy.Stack → List Bool) : Stack → List Bool :=
  fun point => if point = role 0 then small 0 else if point = role 1 then small 1 else
    if point = role 2 then small 2 else if point = role 3 then small 3 else
      if point = role 4 then small 4 else background point

theorem slots_role (role : FieldCopy.Stack → Stack) (injective : Function.Injective role)
    (background : Stack → List Bool) (small : FieldCopy.Stack → List Bool)
    (point : FieldCopy.Stack) : slots role background small (role point) = small point := by
  unfold slots
  simp only [injective.eq_iff]
  fin_cases point <;> rfl

theorem slots_frame (role : FieldCopy.Stack → Stack) (background : Stack → List Bool)
    (small : FieldCopy.Stack → List Bool) (point : Stack)
    (outside : ∀ slot, point ≠ role slot) :
    slots role background small point = background point := by
  simp [slots, outside]

theorem slots_update (role : FieldCopy.Stack → Stack) (injective : Function.Injective role)
    (background : Stack → List Bool) (small : FieldCopy.Stack → List Bool)
    (point : FieldCopy.Stack) (value : List Bool) :
    Function.update (slots role background small) (role point) value =
      slots role background (Function.update small point value) := by
  funext current
  by_cases inside : ∃ index, current = role index
  · obtain ⟨index, rfl⟩ := inside
    by_cases same : index = point
    · subst index
      simp only [Function.update_self, slots_role role injective]
    · have different : role index ≠ role point := fun equality => same (injective equality)
      rw [Function.update_of_ne different, slots_role role injective,
        slots_role role injective, Function.update_of_ne same]
  · have outside : ∀ index, current ≠ role index := fun index same => inside ⟨index, same⟩
    rw [Function.update_of_ne (outside point), slots_frame role background small current outside,
      slots_frame role background (Function.update small point value) current outside]

def configuration {Flags : Type*} (role : FieldCopy.Stack → Stack)
    (labels : FieldCopy.Label → Label) (background : Stack → List Bool)
    (flags : Flags) (small : FieldCopy.State) : State Flags :=
  ⟨small.l.map labels, (small.var, flags), slots role background small.stk⟩

def statement {Flags : Type*} (role : FieldCopy.Stack → Stack) (labels : FieldCopy.Label → Label) :
    TM2.Stmt FieldCopy.Alphabet FieldCopy.Label FieldCopy.Store → Statement Flags
  | .push point value next =>
      .push (role point) (fun memory => value memory.1) (statement role labels next)
  | .peek point value next =>
      .peek (role point) (fun memory bit => (value memory.1 bit, memory.2)) (statement role labels next)
  | .pop point value next =>
      .pop (role point) (fun memory bit => (value memory.1 bit, memory.2)) (statement role labels next)
  | .load value next =>
      .load (fun memory => (value memory.1, memory.2)) (statement role labels next)
  | .branch value yes no =>
      .branch (fun memory => value memory.1) (statement role labels yes) (statement role labels no)
  | .goto value => .goto (fun memory => labels (value memory.1))
  | .halt => .halt

theorem stepAux_configuration {Flags : Type*}
    (role : FieldCopy.Stack → Stack) (injective : Function.Injective role)
    (labels : FieldCopy.Label → Label)
    (code : TM2.Stmt FieldCopy.Alphabet FieldCopy.Label FieldCopy.Store)
    (memory : FieldCopy.Store) (flags : Flags)
    (small : FieldCopy.Stack → List Bool) (background : Stack → List Bool) :
    TM2.stepAux (statement role labels code) (memory, flags) (slots role background small) =
      configuration role labels background flags (TM2.stepAux code memory small) := by
  induction code generalizing memory small with
  | push point value next ih =>
    simp only [statement, TM2.stepAux, slots_role role injective]
    rw [slots_update role injective]
    exact ih _ _
  | peek point value next ih =>
    simp only [statement, TM2.stepAux, slots_role role injective]
    exact ih _ _
  | pop point value next ih =>
    simp only [statement, TM2.stepAux, slots_role role injective]
    rw [slots_update role injective]
    exact ih _ _
  | load value next ih =>
    simp only [statement, TM2.stepAux]
    exact ih _ _
  | branch value yes no yesIH noIH =>
    cases choice : value memory
    · simpa only [statement, TM2.stepAux, choice, Bool.cond_false] using noIH memory small
    · simpa only [statement, TM2.stepAux, choice, Bool.cond_true] using yesIH memory small
  | goto value => rfl
  | halt => rfl

/-- This premise is an equality of fixed syntax, discharged by the
concrete source's phase definitions, not a run/performance oracle. -/
theorem step_configuration {Flags : Type*}
    (role : FieldCopy.Stack → Stack) (injective : Function.Injective role)
    (labels : FieldCopy.Label → Label) (program : Label → Statement Flags)
    (syntaxEq : ∀ point, point ≠ 2 →
      program (labels point) = statement role labels (FieldCopy.program point))
    (background : Stack → List Bool) (flags : Flags) (before after : FieldCopy.State)
    (edge : TM2.step FieldCopy.program before = some after) (active : after.l ≠ none) :
    TM2.step program (configuration role labels background flags before) =
      some (configuration role labels background flags after) := by
  rcases before with ⟨point, memory, small⟩
  cases point with
  | none => simp [TM2.step] at edge
  | some point =>
    have same : TM2.stepAux (FieldCopy.program point) memory small = after := Option.some.inj edge
    change some (TM2.stepAux (program (labels point)) (memory, flags)
      (slots role background small)) = _
    by_cases notTerminal : point = 2
    · subst point
      exact (active (by rw [← same]; rfl)).elim
    · rw [syntaxEq point notTerminal, ← same]
      exact congrArg some (stepAux_configuration role injective labels _ _ _ _ _)

theorem portTrace_chain {Flags : Type*}
    (role : FieldCopy.Stack → Stack) (injective : Function.Injective role)
    (labels : FieldCopy.Label → Label) (program : Label → Statement Flags)
    (syntaxEq : ∀ point, point ≠ 2 →
      program (labels point) = statement role labels (FieldCopy.program point))
    (background : Stack → List Bool) (flags : Flags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    ((FieldCopy.copyPortTrace memory word suffix target).map
      (configuration role labels background flags)).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply (List.isChain_map (configuration role labels background flags)).mpr
  apply List.IsChain.imp_of_mem_imp _ (FieldCopy.copyPortTrace_chain memory word suffix target)
  intro before after _ member edge
  exact step_configuration role injective labels program syntaxEq background flags before after edge
    (BankCopy.copyPortTrace_active _ _ _ _ after member)

end PaperProofs.Common.Native.PSTRWordVM.FieldTransport
