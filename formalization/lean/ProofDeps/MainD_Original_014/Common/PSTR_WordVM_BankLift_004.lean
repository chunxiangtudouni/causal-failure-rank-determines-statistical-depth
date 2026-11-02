module

public import Common.PSTR_WordVM_FieldCopy_003

/-! Actual fixed-bank embedding of the proved five-stack field copier.
The additional caller flags are finite and are framed by every primitive.
The original terminal port becomes a real goto to label 3; the caller
statement at that label is executed only by the following charged step. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.BankCopy

open Turing

abbrev Small := FieldCopy.State
abbrev Stack := Fin 16
abbrev Label := Fin 16
abbrev Alphabet (_ : Stack) := Bool
abbrev Flags := Fin 4
abbrev Store := FieldCopy.Store × Flags
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

/-- These roles are compile-time constants, independent of width and input. -/
def role (slot : FieldCopy.Stack) : Stack :=
  if slot = 0 then 3 else if slot = 1 then 10 else
    if slot = 2 then 11 else if slot = 3 then 7 else 12

def label (point : FieldCopy.Label) : Label := ⟨point.val, by omega⟩

theorem role_injective : Function.Injective role := by decide

def bankStacks (background : Stack → List Bool) (small : FieldCopy.Stack → List Bool) :
    Stack → List Bool :=
  fun slot => if slot = 3 then small 0 else if slot = 10 then small 1 else
    if slot = 11 then small 2 else if slot = 7 then small 3 else
      if slot = 12 then small 4 else background slot

theorem stacks_role (background : Stack → List Bool)
    (small : FieldCopy.Stack → List Bool) (slot : FieldCopy.Stack) :
    bankStacks background small (role slot) = small slot := by
  fin_cases slot <;> rfl

theorem stacks_update (background : Stack → List Bool)
    (small : FieldCopy.Stack → List Bool) (slot : FieldCopy.Stack) (value : List Bool) :
    Function.update (bankStacks background small) (role slot) value =
      bankStacks background (Function.update small slot value) := by
  fin_cases slot <;> funext point <;> fin_cases point <;> rfl

theorem stacks_frame (background : Stack → List Bool)
    (small : FieldCopy.Stack → List Bool) (point : Stack)
    (outside : ∀ slot, point ≠ role slot) :
    bankStacks background small point = background point := by
  have h0 := outside 0
  have h1 := outside 1
  have h2 := outside 2
  have h3 := outside 3
  have h4 := outside 4
  change point ≠ 3 at h0
  change point ≠ 10 at h1
  change point ≠ 11 at h2
  change point ≠ 7 at h3
  change point ≠ 12 at h4
  simp [bankStacks, h0, h1, h2, h3, h4]

def configuration (background : Stack → List Bool) (flags : Flags) (small : Small) : State :=
  ⟨small.l.map label, (small.var, flags), bankStacks background small.stk⟩

def statement : TM2.Stmt FieldCopy.Alphabet FieldCopy.Label FieldCopy.Store → Statement
  | .push slot value next =>
      .push (role slot) (fun memory => value memory.1) (statement next)
  | .peek slot value next =>
      .peek (role slot) (fun memory bit => (value memory.1 bit, memory.2)) (statement next)
  | .pop slot value next =>
      .pop (role slot) (fun memory bit => (value memory.1 bit, memory.2)) (statement next)
  | .load value next =>
      .load (fun memory => (value memory.1, memory.2)) (statement next)
  | .branch value yes no =>
      .branch (fun memory => value memory.1) (statement yes) (statement no)
  | .goto value => .goto (fun memory => label (value memory.1))
  | .halt => .halt

theorem stepAux_configuration
    (code : TM2.Stmt FieldCopy.Alphabet FieldCopy.Label FieldCopy.Store)
    (memory : FieldCopy.Store) (flags : Flags)
    (small : FieldCopy.Stack → List Bool) (background : Stack → List Bool) :
    TM2.stepAux (statement code) (memory, flags) (bankStacks background small) =
      configuration background flags (TM2.stepAux code memory small) := by
  induction code generalizing memory small with
  | push slot value next ih =>
    simp only [statement, TM2.stepAux, stacks_role]
    rw [stacks_update]
    exact ih _ _
  | peek slot value next ih =>
    simp only [statement, TM2.stepAux, stacks_role]
    exact ih _ _
  | pop slot value next ih =>
    simp only [statement, TM2.stepAux, stacks_role]
    rw [stacks_update]
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

/-- `caller` is fixed program syntax. It is not a runtime input or a
performance premise. Labels 0, 1 and 2 are reserved for this macro. -/
def program (caller : Label → Statement) (point : Label) : Statement :=
  if point = 0 then statement (FieldCopy.program 0) else
    if point = 1 then statement (FieldCopy.program 1) else
      if point = 2 then .goto (fun _ => 3) else caller point

theorem step_configuration (caller : Label → Statement)
    (background : Stack → List Bool) (flags : Flags) (before after : Small)
    (edge : TM2.step FieldCopy.program before = some after) (active : after.l ≠ none) :
    TM2.step (program caller) (configuration background flags before) =
      some (configuration background flags after) := by
  rcases before with ⟨point, memory, small⟩
  cases point with
  | none => simp [TM2.step] at edge
  | some point =>
    have same : TM2.stepAux (FieldCopy.program point) memory small = after := Option.some.inj edge
    fin_cases point
    · rw [← same]
      change some (TM2.stepAux (statement (FieldCopy.program 0))
        (memory, flags) (bankStacks background small)) = _
      exact congrArg some (stepAux_configuration _ _ _ _ _)
    · rw [← same]
      change some (TM2.stepAux (statement (FieldCopy.program 1))
        (memory, flags) (bankStacks background small)) = _
      exact congrArg some (stepAux_configuration _ _ _ _ _)
    · exact (active (by rw [← same]; rfl)).elim

def returned (background : Stack → List Bool) (flags : Flags)
    (word suffix target : List Bool) : State :=
  ⟨some 3, ((false, false), flags),
    bankStacks background (FieldCopy.copyPort word suffix target).stk⟩

theorem return_edge (caller : Label → Statement) (background : Stack → List Bool)
    (flags : Flags) (word suffix target : List Bool) :
    TM2.step (program caller)
      (configuration background flags (FieldCopy.copyPort word suffix target)) =
      some (returned background flags word suffix target) := rfl

theorem caller_entry (caller : Label → Statement) (background : Stack → List Bool)
    (flags : Flags) (word suffix target : List Bool) :
    TM2.step (program caller) (returned background flags word suffix target) =
      some (TM2.stepAux (caller 3) (returned background flags word suffix target).var
        (returned background flags word suffix target).stk) := rfl

def outsideOccupied (background : Stack → List Bool) : Nat :=
  (background 0).length + (background 1).length + (background 2).length +
    (background 4).length + (background 5).length + (background 6).length +
    (background 8).length + (background 9).length + (background 13).length +
    (background 14).length + (background 15).length

def occupied (current : State) : Nat :=
  (current.stk 0).length + (current.stk 1).length + (current.stk 2).length +
    (current.stk 3).length + (current.stk 4).length + (current.stk 5).length +
    (current.stk 6).length + (current.stk 7).length + (current.stk 8).length +
    (current.stk 9).length + (current.stk 10).length + (current.stk 11).length +
    (current.stk 12).length + (current.stk 13).length + (current.stk 14).length +
    (current.stk 15).length

theorem occupied_configuration (background : Stack → List Bool) (flags : Flags) (small : Small) :
    occupied (configuration background flags small) =
      outsideOccupied background + FieldCopy.occupied small := by
  unfold occupied configuration outsideOccupied FieldCopy.occupied
  change (background 0).length + (background 1).length + (background 2).length +
    (small.stk 0).length + (background 4).length + (background 5).length +
    (background 6).length + (small.stk 3).length + (background 8).length +
    (background 9).length + (small.stk 1).length + (small.stk 2).length +
    (small.stk 4).length + (background 13).length + (background 14).length +
    (background 15).length = _
  omega

theorem returned_occupied (background : Stack → List Bool) (flags : Flags)
    (word suffix target : List Bool) :
    occupied (returned background flags word suffix target) =
      outsideOccupied background + 3 * word.length + suffix.length + target.length := by
  change occupied (configuration background flags (FieldCopy.copyPort word suffix target)) = _
  rw [occupied_configuration]
  simp only [FieldCopy.copyPort, FieldCopy.occupied_state, List.length_append,
    List.length_replicate, List.length_nil]
  omega

end PaperProofs.Common.Native.PSTRWordVM.BankCopy
