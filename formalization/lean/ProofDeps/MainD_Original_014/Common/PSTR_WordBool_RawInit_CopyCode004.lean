module

public import Common.PSTR_WordBool_RawInit_Gate003

/-! Fixed physical single-header copier code. The original unread head
bit is genuinely captured in finite control and temporarily written false.
The work counter is copied into a separate far-left flagged bank; each
selected work flag is restored before selecting the next one. No length,
counter value or output word is an argument to either transition table.
Trace correctness and the complete copier endpoint are subsequent lemmas. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.HeaderCopy

open Turing PaperProofs.Common.Native.RationalControllerComputation

def roundLabel (saved : Bool) (phase : Fin 18) : Fin 42 :=
  ⟨(if saved then 24 else 6) + phase.val, by
    have hp := phase.isLt
    cases saved <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩

def roundCode (saved : Bool) (phase : Nat) (symbol : Bool) :
    Option (Fin 42 × TM0.Stmt Bool) :=
  match phase with
  | 0 => some (roundLabel saved 1, .write false)
  | 1 => some (roundLabel saved 2, .move .left)
  | 2 => some (roundLabel saved 3, .move .left)
  | 3 => some (roundLabel saved (if symbol then 4 else 5), .move .left)
  | 4 => some (roundLabel saved 3, .move .left)
  | 5 => some (roundLabel saved 6, .move .left)
  | 6 => if symbol then some (roundLabel saved 7, .move .left)
      else some (roundLabel saved 8, .write true)
  | 7 => some (roundLabel saved 6, .move .left)
  | 8 => some (roundLabel saved 9, .move .left)
  | 9 => some (roundLabel saved 10, .write saved)
  | 10 => some (roundLabel saved 11, .move .right)
  | 11 => some (roundLabel saved (if symbol then 12 else 14), .move .right)
  | 12 => some (roundLabel saved 11, .move .right)
  | 14 => some (roundLabel saved 15, .move .right)
  | 15 => if symbol then some (roundLabel saved 14, .move .right)
      else some (roundLabel saved 16, .write true)
  | 16 => some (roundLabel saved 17, .move .left)
  | 17 => some (2, .move .left)
  | _ => none

def coreMachine : Machine 41 := fun q symbol =>
  match q.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .move .left)
  | 2 => if symbol then some (3, .move .left) else some (4, .move .right)
  | 3 => some (roundLabel symbol 0, .move .right)
  | 4 => some (5, .move .right)
  | 5 => if symbol then some (4, .move .right) else none
  | label =>
    let saved := decide (24 ≤ label)
    roundCode saved (label - (if saved then 24 else 6)) symbol

def coreState (q : Fin 42) (left right : List Bool) : MachineState 41 :=
  ⟨q, Tape.mk₂ left right⟩

theorem round_lookup (saved : Bool) (phase : Fin 18) (symbol : Bool) :
    coreMachine (roundLabel saved phase) symbol = roundCode saved phase.val symbol := by
  fin_cases phase <;> cases saved <;> rfl

def bodyLabel (originalHead : Bool) (q : Fin 42) : Fin 86 :=
  ⟨(if originalHead then 43 else 1) + q.val, by
    have bound := q.isLt
    cases originalHead <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩

def bodyCfg (originalHead : Bool) (cfg : MachineState 41) : MachineState 85 :=
  ⟨bodyLabel originalHead cfg.q, cfg.Tape⟩

def machine : Machine 85 := fun q symbol =>
  if initial : q.val = 0 then some (bodyLabel symbol 0, .write false)
  else if body : q.val < 85 then
    let originalHead := decide (43 ≤ q.val)
    let point : Fin 42 := ⟨(q.val - 1) % 42, Nat.mod_lt _ (by decide)⟩
    match coreMachine point symbol with
    | none => some (85, .write originalHead)
    | some (next, op) => some (bodyLabel originalHead next, op)
  else none

def state (q : Fin 86) (left right : List Bool) : MachineState 85 :=
  ⟨q, Tape.mk₂ left right⟩

theorem body_lookup (originalHead : Bool) (q : Fin 42) (symbol : Bool) :
    machine (bodyLabel originalHead q) symbol =
      match coreMachine q symbol with
      | none => some (85, .write originalHead)
      | some (next, op) => some (bodyLabel originalHead next, op) := by
  fin_cases q <;> cases originalHead <;> rfl

theorem capture_step (left tail : List Bool) (originalHead : Bool) :
    TM0.step machine (state 0 left (originalHead :: tail)) =
      some (state (bodyLabel originalHead 0) left (false :: tail)) := by
  cases originalHead <;> simp [TM0.step, machine, state, Tape.mk₂]

theorem body_step (originalHead : Bool) (cfg : MachineState 41) :
    TM0.step machine (bodyCfg originalHead cfg) =
      match TM0.step coreMachine cfg with
      | none => some ⟨85, cfg.Tape.write originalHead⟩
      | some next => some (bodyCfg originalHead next) := by
  cases cfg with
  | mk q tape =>
    simp only [TM0.step, bodyCfg]
    rw [body_lookup]
    cases action : coreMachine q tape.head with
    | none => rfl
    | some pair =>
      obtain ⟨next, op⟩ := pair
      cases op <;> rfl

theorem final_halt (left right : List Bool) :
    TM0.step machine (state 85 left right) = none := by
  simp [TM0.step, machine, state]

end PaperProofs.Common.Native.PSTRWordBool.RawInit.HeaderCopy
